/* This file is part of the dynarmic project.
 * Copyright (c) 2016 MerryMage
 * This software may be used and distributed according to the terms of the GNU
 * General Public License version 2 or any later version.
 */

#include <type_traits>
#include <utility>

#include "backend/x64/abi.h"
#include "backend/x64/block_of_code.h"
#include "backend/x64/emit_x64.h"
#include "common/assert.h"
#include "common/common_types.h"
#include "common/fp/fpcr.h"
#include "common/fp/fpsr.h"
#include "common/fp/info.h"
#include "common/fp/op.h"
#include "common/fp/rounding_mode.h"
#include "common/fp/util.h"
#include "common/mp/cartesian_product.h"
#include "common/mp/integer.h"
#include "common/mp/list.h"
#include "common/mp/lut.h"
#include "common/mp/to_tuple.h"
#include "common/mp/vlift.h"
#include "common/mp/vllift.h"
#include "frontend/ir/basic_block.h"
#include "frontend/ir/microinstruction.h"
#include "frontend/ir/opcodes.h"

namespace Dynarmic::BackendX64 {

using namespace Xbyak::util;
namespace mp = Dynarmic::Common::mp;

namespace {

const Xbyak::Reg64 INVALID_REG = Xbyak::Reg64(-1);

constexpr u64 f32_negative_zero = 0x80000000u;
constexpr u64 f32_nan = 0x7fc00000u;
constexpr u64 f32_non_sign_mask = 0x7fffffffu;
constexpr u64 f32_smallest_normal = 0x00800000u;

constexpr u64 f64_negative_zero = 0x8000000000000000u;
constexpr u64 f64_nan = 0x7ff8000000000000u;
constexpr u64 f64_non_sign_mask = 0x7fffffffffffffffu;
constexpr u64 f64_smallest_normal = 0x0010000000000000u;

constexpr u64 f64_penultimate_positive_denormal = 0x000ffffffffffffeu;
constexpr u64 f64_max_s32 = 0x41dfffffffc00000u; // 2147483647 as a double
constexpr u64 f64_min_u32 = 0x0000000000000000u; // 0 as a double
constexpr u64 f64_max_u32 = 0x41efffffffe00000u; // 4294967295 as a double
constexpr u64 f64_max_s64_lim = 0x43e0000000000000u; // 2^63 as a double (actual maximum unrepresentable)
constexpr u64 f64_min_u64 = 0x0000000000000000u; // 0 as a double
constexpr u64 f64_max_u64_lim = 0x43f0000000000000u; // 2^64 as a double (actual maximum unrepresentable)

template<size_t fsize, typename T>
T ChooseOnFsize([[maybe_unused]] T f32, [[maybe_unused]] T f64) {
    static_assert(fsize == 32 || fsize == 64, "fsize must be either 32 or 64");

    if constexpr (fsize == 32) {
        return f32;
    } else {
        return f64;
    }
}

#define FCODE(NAME) (code.*ChooseOnFsize<fsize>(&Xbyak::CodeGenerator::NAME##s, &Xbyak::CodeGenerator::NAME##d))

template<size_t fsize>
void DenormalsAreZero(BlockOfCode& code, Xbyak::Xmm xmm_value, Xbyak::Reg64 gpr_scratch) {
    Xbyak::Label end;

    if constexpr (fsize == 32) {
        code.movd(gpr_scratch.cvt32(), xmm_value);
        code.and_(gpr_scratch.cvt32(), u32(0x7FFFFFFF));
        code.sub(gpr_scratch.cvt32(), u32(1));
        code.cmp(gpr_scratch.cvt32(), u32(0x007FFFFE));
    } else {
        auto mask = code.MConst(xword, f64_non_sign_mask);
        mask.setBit(64);
        auto penult_denormal = code.MConst(xword, f64_penultimate_positive_denormal);
        penult_denormal.setBit(64);

        code.movq(gpr_scratch, xmm_value);
        code.and_(gpr_scratch, mask);
        code.sub(gpr_scratch, u32(1));
        code.cmp(gpr_scratch, penult_denormal);
    }

    // We need to report back whether we've found a denormal on input.
    // SSE doesn't do this for us when SSE's DAZ is enabled.

    code.ja(end);
    code.andps(xmm_value, code.MConst(xword, fsize == 32 ? f32_negative_zero : f64_negative_zero));
    code.mov(dword[r15 + code.GetJitStateInfo().offsetof_FPSCR_IDC], u32(1 << 7));
    code.L(end);
}

template<size_t fsize>
void ZeroIfNaN(BlockOfCode& code, Xbyak::Xmm xmm_value, Xbyak::Xmm xmm_scratch) {
    code.xorps(xmm_scratch, xmm_scratch);
    FCODE(cmpords)(xmm_scratch, xmm_value); // true mask when ordered (i.e.: when not an NaN)
    code.pand(xmm_value, xmm_scratch);
}

template<size_t fsize>
void ForceToDefaultNaN(BlockOfCode& code, Xbyak::Xmm result) {
    if (code.DoesCpuSupport(Xbyak::util::Cpu::tAVX)) {
        FCODE(vcmpunords)(xmm0, result, result);
        FCODE(blendvp)(result, code.MConst(xword, fsize == 32 ? f32_nan : f64_nan));
    } else {
        Xbyak::Label end;
        FCODE(ucomis)(result, result);
        code.jnp(end);
        code.movaps(result, code.MConst(xword, fsize == 32 ? f32_nan : f64_nan));
        code.L(end);
    }
}

template<size_t fsize>
Xbyak::Label ProcessNaN(BlockOfCode& code, Xbyak::Xmm a) {
    Xbyak::Label nan, end;

    FCODE(ucomis)(a, a);
    code.jp(nan, code.T_NEAR);
    code.SwitchToFarCode();
    code.L(nan);

    code.orps(a, code.MConst(xword, fsize == 32 ? 0x00400000 : 0x0008'0000'0000'0000));

    code.jmp(end, code.T_NEAR);
    code.SwitchToNearCode();
    return end;
}

template<size_t fsize>
void PostProcessNaN(BlockOfCode& code, Xbyak::Xmm result, Xbyak::Xmm tmp) {
    if constexpr (fsize == 32) {
        code.movaps(tmp, result);
        code.cmpunordps(tmp, tmp);
        code.pslld(tmp, 31);
        code.xorps(result, tmp);
    } else {
        code.movaps(tmp, result);
        code.cmpunordpd(tmp, tmp);
        code.psllq(tmp, 63);
        code.xorps(result, tmp);
    }
}

// This is necessary because x86 and ARM differ in they way they return NaNs from floating point operations
//
// ARM behaviour:
// op1         op2          result
// SNaN        SNaN/QNaN    op1
// QNaN        SNaN         op2
// QNaN        QNaN         op1
// SNaN/QNaN   other        op1
// other       SNaN/QNaN    op2
//
// x86 behaviour:
// op1         op2          result
// SNaN/QNaN   SNaN/QNaN    op1
// SNaN/QNaN   other        op1
// other       SNaN/QNaN    op2
//
// With ARM: SNaNs take priority. With x86: it doesn't matter.
//
// From the above we can see what differs between the architectures is
// the case when op1 == QNaN and op2 == SNaN.
//
// We assume that registers op1 and op2 are read-only. This function also trashes xmm0.
// We allow for the case where op1 and result are the same register. We do not read from op1 once result is written to.
template<size_t fsize>
void EmitPostProcessNaNs(BlockOfCode& code, Xbyak::Xmm result, Xbyak::Xmm op1, Xbyak::Xmm op2, Xbyak::Reg64 tmp, Xbyak::Label end) {
    using FPT = mp::unsigned_integer_of_size<fsize>;
    constexpr FPT exponent_mask = FP::FPInfo<FPT>::exponent_mask;
    constexpr FPT mantissa_msb = FP::FPInfo<FPT>::mantissa_msb;
    constexpr u8 mantissa_msb_bit = static_cast<u8>(FP::FPInfo<FPT>::explicit_mantissa_width - 1);

    // At this point we know that at least one of op1 and op2 is a NaN.
    // Thus in op1 ^ op2 at least one of the two would have all 1 bits in the exponent.
    // Keeping in mind xor is commutative, there are only four cases:
    // SNaN      ^ SNaN/Inf  -> exponent == 0, mantissa_msb == 0
    // QNaN      ^ QNaN      -> exponent == 0, mantissa_msb == 0
    // QNaN      ^ SNaN/Inf  -> exponent == 0, mantissa_msb == 1
    // SNaN/QNaN ^ Otherwise -> exponent != 0, mantissa_msb == ?
    //
    // We're only really interested in op1 == QNaN and op2 == SNaN,
    // so we filter out everything else.
    //
    // We do it this way instead of checking that op1 is QNaN because
    // op1 == QNaN && op2 == QNaN is the most common case. With this method
    // that case would only require one branch.

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tAVX)) {
        code.vxorps(xmm0, op1, op2);
    } else {
        code.movaps(xmm0, op1);
        code.xorps(xmm0, op2);
    }

    constexpr size_t shift = fsize == 32 ? 0 : 48;
    if constexpr (fsize == 32) {
        code.movd(tmp.cvt32(), xmm0);
    } else {
        // We do this to avoid requiring 64-bit immediates
        code.pextrw(tmp.cvt32(), xmm0, shift / 16);
    }
    code.and_(tmp.cvt32(), static_cast<u32>((exponent_mask | mantissa_msb) >> shift));
    code.cmp(tmp.cvt32(), static_cast<u32>(mantissa_msb >> shift));
    code.jne(end, code.T_NEAR);

    // If we're here there are four cases left:
    // op1 == SNaN && op2 == QNaN
    // op1 == Inf  && op2 == QNaN
    // op1 == QNaN && op2 == SNaN <<< The problematic case
    // op1 == QNaN && op2 == Inf

    if constexpr (fsize == 32) {
        code.movd(tmp.cvt32(), op2);
        code.shl(tmp.cvt32(), 32 - mantissa_msb_bit);
    } else {
        code.movq(tmp, op2);
        code.shl(tmp, 64 - mantissa_msb_bit);
    }
    // If op2 is a SNaN, CF = 0 and ZF = 0.
    code.jna(end, code.T_NEAR);

    // Silence the SNaN as required by spec.
    if (code.DoesCpuSupport(Xbyak::util::Cpu::tAVX)) {
        code.vorps(result, op2, code.MConst(xword, mantissa_msb));
    } else {
        code.movaps(result, op2);
        code.orps(result, code.MConst(xword, mantissa_msb));
    }
    code.jmp(end, code.T_NEAR);
}

template <size_t fsize, typename Function>
void FPTwoOp(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst, Function fn) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    Xbyak::Label end;

    Xbyak::Xmm result = ctx.reg_alloc.UseScratchXmm(args[0]);

    if (ctx.AccurateNaN() && !ctx.FPSCR_DN()) {
        end = ProcessNaN<fsize>(code, result);
    }
    if constexpr (std::is_member_function_pointer_v<Function>) {
        (code.*fn)(result, result);
    } else {
        fn(result);
    }
    if (ctx.FPSCR_DN()) {
        ForceToDefaultNaN<fsize>(code, result);
    } else if (ctx.AccurateNaN()) {
        PostProcessNaN<fsize>(code, result, ctx.reg_alloc.ScratchXmm());
    }
    code.L(end);

    ctx.reg_alloc.DefineValue(inst, result);
}

template <size_t fsize, typename Function>
void FPThreeOp(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst, Function fn) {
    using FPT = mp::unsigned_integer_of_size<fsize>;

    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    if (ctx.FPSCR_DN() || !ctx.AccurateNaN()) {
        const Xbyak::Xmm result = ctx.reg_alloc.UseScratchXmm(args[0]);
        const Xbyak::Xmm operand = ctx.reg_alloc.UseScratchXmm(args[1]);

        if constexpr (std::is_member_function_pointer_v<Function>) {
            (code.*fn)(result, operand);
        } else {
            fn(result, operand);
        }

        if (ctx.AccurateNaN()) {
            ForceToDefaultNaN<fsize>(code, result);
        }

        ctx.reg_alloc.DefineValue(inst, result);
        return;
    }

    const Xbyak::Xmm op1 = ctx.reg_alloc.UseXmm(args[0]);
    const Xbyak::Xmm op2 = ctx.reg_alloc.UseXmm(args[1]);
    const Xbyak::Xmm result = ctx.reg_alloc.ScratchXmm();
    const Xbyak::Reg64 tmp = ctx.reg_alloc.ScratchGpr();

    Xbyak::Label end, nan, op_are_nans;

    code.movaps(result, op1);
    if constexpr (std::is_member_function_pointer_v<Function>) {
        (code.*fn)(result, op2);
    } else {
        fn(result, op2);
    }
    FCODE(ucomis)(result, result);
    code.jp(nan, code.T_NEAR);
    code.L(end);

    code.SwitchToFarCode();
    code.L(nan);
    FCODE(ucomis)(op1, op2);
    code.jp(op_are_nans);
    // Here we must return a positive NaN, because the indefinite value on x86 is a negative NaN!
    code.movaps(result, code.MConst(xword, FP::FPInfo<FPT>::DefaultNaN()));
    code.jmp(end, code.T_NEAR);
    code.L(op_are_nans);
    EmitPostProcessNaNs<fsize>(code, result, op1, op2, tmp, end);
    code.SwitchToNearCode();

    ctx.reg_alloc.DefineValue(inst, result);
}

} // anonymous namespace

void EmitX64::EmitFPAbs32(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    Xbyak::Xmm result = ctx.reg_alloc.UseScratchXmm(args[0]);

    code.pand(result, code.MConst(xword, f32_non_sign_mask));

    ctx.reg_alloc.DefineValue(inst, result);
}

void EmitX64::EmitFPAbs64(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    Xbyak::Xmm result = ctx.reg_alloc.UseScratchXmm(args[0]);

    code.pand(result, code.MConst(xword, f64_non_sign_mask));

    ctx.reg_alloc.DefineValue(inst, result);
}

void EmitX64::EmitFPNeg32(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    Xbyak::Xmm result = ctx.reg_alloc.UseScratchXmm(args[0]);

    code.pxor(result, code.MConst(xword, f32_negative_zero));

    ctx.reg_alloc.DefineValue(inst, result);
}

void EmitX64::EmitFPNeg64(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    Xbyak::Xmm result = ctx.reg_alloc.UseScratchXmm(args[0]);

    code.pxor(result, code.MConst(xword, f64_negative_zero));

    ctx.reg_alloc.DefineValue(inst, result);
}

void EmitX64::EmitFPAdd32(EmitContext& ctx, IR::Inst* inst) {
    FPThreeOp<32>(code, ctx, inst, &Xbyak::CodeGenerator::addss);
}

void EmitX64::EmitFPAdd64(EmitContext& ctx, IR::Inst* inst) {
    FPThreeOp<64>(code, ctx, inst, &Xbyak::CodeGenerator::addsd);
}

void EmitX64::EmitFPDiv32(EmitContext& ctx, IR::Inst* inst) {
    FPThreeOp<32>(code, ctx, inst, &Xbyak::CodeGenerator::divss);
}

void EmitX64::EmitFPDiv64(EmitContext& ctx, IR::Inst* inst) {
    FPThreeOp<64>(code, ctx, inst, &Xbyak::CodeGenerator::divsd);
}

template<size_t fsize, bool is_max>
static void EmitFPMinMax(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const Xbyak::Xmm result = ctx.reg_alloc.UseScratchXmm(args[0]);
    const Xbyak::Xmm operand = ctx.reg_alloc.UseScratchXmm(args[1]);
    const Xbyak::Xmm tmp = ctx.reg_alloc.ScratchXmm();
    const Xbyak::Reg64 gpr_scratch = ctx.reg_alloc.ScratchGpr();

    if (ctx.FPSCR_FTZ()) {
        DenormalsAreZero<fsize>(code, result, gpr_scratch);
        DenormalsAreZero<fsize>(code, operand, gpr_scratch);
    }

    Xbyak::Label equal, end, nan;

    FCODE(ucomis)(result, operand);
    code.jz(equal, code.T_NEAR);
    if constexpr (is_max) {
        FCODE(maxs)(result, operand);
    } else {
        FCODE(mins)(result, operand);
    }
    code.L(end);

    code.SwitchToFarCode();

    code.L(equal);
    code.jp(nan);
    if constexpr (is_max) {
        code.andps(result, operand);
    } else {
        code.orps(result, operand);
    }
    code.jmp(end);

    code.L(nan);
    if (ctx.FPSCR_DN() || !ctx.AccurateNaN()) {
        code.movaps(result, code.MConst(xword, fsize == 32 ? f32_nan : f64_nan));
        code.jmp(end);
    } else {
        code.movaps(tmp, result);
        FCODE(adds)(result, operand);
        EmitPostProcessNaNs<fsize>(code, result, tmp, operand, gpr_scratch, end);
    }

    code.SwitchToNearCode();

    ctx.reg_alloc.DefineValue(inst, result);
}

template<size_t fsize, bool is_max>
static void EmitFPMinMaxNumeric(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst) {
    using FPT = mp::unsigned_integer_of_size<fsize>;
    constexpr u8 mantissa_msb_bit = static_cast<u8>(FP::FPInfo<FPT>::explicit_mantissa_width - 1);

    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const Xbyak::Xmm op1 = ctx.reg_alloc.UseScratchXmm(args[0]);
    const Xbyak::Xmm op2 = ctx.reg_alloc.UseScratchXmm(args[1]); // Result stored here!
    Xbyak::Reg tmp = ctx.reg_alloc.ScratchGpr();
    tmp.setBit(fsize);

    const auto move_to_tmp = [&](const Xbyak::Xmm& xmm) {
        if constexpr (fsize == 32) {
            code.movd(tmp.cvt32(), xmm);
        } else {
            code.movq(tmp.cvt64(), xmm);
        }
    };

    if (ctx.FPSCR_FTZ()) {
        DenormalsAreZero<fsize>(code, op1, tmp.cvt64());
        DenormalsAreZero<fsize>(code, op2, tmp.cvt64());
    }

    Xbyak::Label end, z, nan, op2_is_nan, snan, maybe_both_nan, normal;

    FCODE(ucomis)(op1, op2);
    code.jz(z, code.T_NEAR);
    code.L(normal);
    if constexpr (is_max) {
        FCODE(maxs)(op2, op1);
    } else {
        FCODE(mins)(op2, op1);
    }
    code.L(end);

    code.SwitchToFarCode();

    code.L(z);
    code.jp(nan);
    if constexpr (is_max) {
        code.andps(op2, op1);
    } else {
        code.orps(op2, op1);
    }
    code.jmp(end);

    // NaN requirements:
    // op1     op2      result
    // SNaN    anything op1
    // !SNaN   SNaN     op2
    // QNaN    !NaN     op2
    // !NaN    QNaN     op1
    // QNaN    QNaN     op1

    code.L(nan);
    FCODE(ucomis)(op1, op1);
    code.jnp(op2_is_nan);

    // op1 is NaN
    move_to_tmp(op1);
    code.bt(tmp, mantissa_msb_bit);
    code.jc(maybe_both_nan);
    if (ctx.FPSCR_DN()) {
        code.L(snan);
        code.movaps(op2, code.MConst(xword, FP::FPInfo<FPT>::DefaultNaN()));
        code.jmp(end);
    } else {
        code.movaps(op2, op1);
        code.L(snan);
        code.orps(op2, code.MConst(xword, FP::FPInfo<FPT>::mantissa_msb));
        code.jmp(end);
    }

    code.L(maybe_both_nan);
    FCODE(ucomis)(op2, op2);
    code.jnp(end, code.T_NEAR);
    if (ctx.FPSCR_DN()) {
        code.jmp(snan);
    } else {
        move_to_tmp(op2);
        code.bt(tmp.cvt64(), mantissa_msb_bit);
        code.jnc(snan);
        code.movaps(op2, op1);
        code.jmp(end);
    }

    // op2 is NaN
    code.L(op2_is_nan);
    move_to_tmp(op2);
    code.bt(tmp, mantissa_msb_bit);
    code.jnc(snan);
    code.movaps(op2, op1);
    code.jmp(end);

    code.SwitchToNearCode();

    ctx.reg_alloc.DefineValue(inst, op2);
}

void EmitX64::EmitFPMax32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMinMax<32, true>(code, ctx, inst);
}

void EmitX64::EmitFPMax64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMinMax<64, true>(code, ctx, inst);
}

void EmitX64::EmitFPMaxNumeric32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMinMaxNumeric<32, true>(code, ctx, inst);
}

void EmitX64::EmitFPMaxNumeric64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMinMaxNumeric<64, true>(code, ctx, inst);
}

void EmitX64::EmitFPMin32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMinMax<32, false>(code, ctx, inst);
}

void EmitX64::EmitFPMin64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMinMax<64, false>(code, ctx, inst);
}

void EmitX64::EmitFPMinNumeric32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMinMaxNumeric<32, false>(code, ctx, inst);
}

void EmitX64::EmitFPMinNumeric64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMinMaxNumeric<64, false>(code, ctx, inst);
}

void EmitX64::EmitFPMul32(EmitContext& ctx, IR::Inst* inst) {
    FPThreeOp<32>(code, ctx, inst, &Xbyak::CodeGenerator::mulss);
}

void EmitX64::EmitFPMul64(EmitContext& ctx, IR::Inst* inst) {
    FPThreeOp<64>(code, ctx, inst, &Xbyak::CodeGenerator::mulsd);
}

template<size_t fsize>
static void EmitFPMulAdd(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst) {
    using FPT = mp::unsigned_integer_of_size<fsize>;

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tFMA)) {
        auto args = ctx.reg_alloc.GetArgumentInfo(inst);

        Xbyak::Label end, fallback;

        const Xbyak::Xmm operand1 = ctx.reg_alloc.UseXmm(args[0]);
        const Xbyak::Xmm operand2 = ctx.reg_alloc.UseXmm(args[1]);
        const Xbyak::Xmm operand3 = ctx.reg_alloc.UseXmm(args[2]);
        const Xbyak::Xmm result = ctx.reg_alloc.ScratchXmm();
        const Xbyak::Xmm tmp = ctx.reg_alloc.ScratchXmm();

        code.movaps(result, operand1);
        FCODE(vfmadd231s)(result, operand2, operand3);

        code.movaps(tmp, code.MConst(xword, fsize == 32 ? f32_non_sign_mask : f64_non_sign_mask));
        code.andps(tmp, result);
        FCODE(ucomis)(tmp, code.MConst(xword, fsize == 32 ? f32_smallest_normal : f64_smallest_normal));
        code.jz(fallback, code.T_NEAR);
        code.L(end);

        code.SwitchToFarCode();
        code.L(fallback);

        code.sub(rsp, 8);
        ABI_PushCallerSaveRegistersAndAdjustStackExcept(code, HostLocXmmIdx(result.getIdx()));
        code.movq(code.ABI_PARAM1, operand1);
        code.movq(code.ABI_PARAM2, operand2);
        code.movq(code.ABI_PARAM3, operand3);
        code.mov(code.ABI_PARAM4.cvt32(), ctx.FPCR());
#ifdef _WIN32
        code.sub(rsp, 16 + ABI_SHADOW_SPACE);
        code.lea(rax, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
        code.mov(qword[rsp + ABI_SHADOW_SPACE], rax);
        code.CallFunction(&FP::FPMulAdd<FPT>);
        code.add(rsp, 16 + ABI_SHADOW_SPACE);
#else
        code.lea(code.ABI_PARAM5, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
        code.CallFunction(&FP::FPMulAdd<FPT>);
#endif
        code.movq(result, code.ABI_RETURN);
        ABI_PopCallerSaveRegistersAndAdjustStackExcept(code, HostLocXmmIdx(result.getIdx()));
        code.add(rsp, 8);

        code.jmp(end, code.T_NEAR);
        code.SwitchToNearCode();

        ctx.reg_alloc.DefineValue(inst, result);
        return;
    }

    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    ctx.reg_alloc.HostCall(inst, args[0], args[1], args[2]);
    code.mov(code.ABI_PARAM4.cvt32(), ctx.FPCR());
#ifdef _WIN32
    code.sub(rsp, 16 + ABI_SHADOW_SPACE);
    code.lea(rax, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
    code.mov(qword[rsp + ABI_SHADOW_SPACE], rax);
    code.CallFunction(&FP::FPMulAdd<FPT>);
    code.add(rsp, 16 + ABI_SHADOW_SPACE);
#else
    code.lea(code.ABI_PARAM5, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
    code.CallFunction(&FP::FPMulAdd<FPT>);
#endif
}

void EmitX64::EmitFPMulAdd32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMulAdd<32>(code, ctx, inst);
}

void EmitX64::EmitFPMulAdd64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMulAdd<64>(code, ctx, inst);
}

template<size_t fsize>
static void EmitFPMulX(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst) {
    using FPT = mp::unsigned_integer_of_size<fsize>;

    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const bool do_default_nan = ctx.FPSCR_DN() || !ctx.AccurateNaN();

    const Xbyak::Xmm op1 = ctx.reg_alloc.UseXmm(args[0]);
    const Xbyak::Xmm op2 = ctx.reg_alloc.UseXmm(args[1]);
    const Xbyak::Xmm result = ctx.reg_alloc.ScratchXmm();
    const Xbyak::Reg64 tmp = do_default_nan ? INVALID_REG : ctx.reg_alloc.ScratchGpr();

    Xbyak::Label end, nan, op_are_nans;

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tAVX)) {
        FCODE(vmuls)(result, op1, op2);
    } else {
        code.movaps(result, op1);
        FCODE(muls)(result, op2);
    }
    FCODE(ucomis)(result, result);
    code.jp(nan, code.T_NEAR);
    code.L(end);

    code.SwitchToFarCode();
    code.L(nan);
    FCODE(ucomis)(op1, op2);
    code.jp(op_are_nans);
    if (code.DoesCpuSupport(Xbyak::util::Cpu::tAVX)) {
        code.vxorps(result, op1, op2);
    } else {
        code.movaps(result, op1);
        code.xorps(result, op2);
    }
    code.andps(result, code.MConst(xword, FP::FPInfo<FPT>::sign_mask));
    code.orps(result, code.MConst(xword, FP::FPValue<FPT, false, 0, 2>()));
    code.jmp(end, code.T_NEAR);
    code.L(op_are_nans);
    if (do_default_nan) {
        code.movaps(result, code.MConst(xword, FP::FPInfo<FPT>::DefaultNaN()));
        code.jmp(end, code.T_NEAR);
    } else {
        EmitPostProcessNaNs<fsize>(code, result, op1, op2, tmp, end);
    }
    code.SwitchToNearCode();

    ctx.reg_alloc.DefineValue(inst, result);
}

void EmitX64::EmitFPMulX32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMulX<32>(code, ctx, inst);
}

void EmitX64::EmitFPMulX64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPMulX<64>(code, ctx, inst);
}

template<typename FPT>
static void EmitFPRecipEstimate(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    ctx.reg_alloc.HostCall(inst, args[0]);
    code.mov(code.ABI_PARAM2.cvt32(), ctx.FPCR());
    code.lea(code.ABI_PARAM3, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
    code.CallFunction(&FP::FPRecipEstimate<FPT>);
}

void EmitX64::EmitFPRecipEstimate32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRecipEstimate<u32>(code, ctx, inst);
}

void EmitX64::EmitFPRecipEstimate64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRecipEstimate<u64>(code, ctx, inst);
}

template<size_t fsize>
static void EmitFPRecipStepFused(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst) {
    using FPT = mp::unsigned_integer_of_size<fsize>;

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tFMA)) {
        auto args = ctx.reg_alloc.GetArgumentInfo(inst);

        Xbyak::Label end, fallback;

        const Xbyak::Xmm operand1 = ctx.reg_alloc.UseXmm(args[0]);
        const Xbyak::Xmm operand2 = ctx.reg_alloc.UseXmm(args[1]);
        const Xbyak::Xmm result = ctx.reg_alloc.ScratchXmm();

        code.movaps(result, code.MConst(xword, FP::FPValue<FPT, false, 0, 2>()));
        FCODE(vfnmadd231s)(result, operand1, operand2);
        FCODE(ucomis)(result, result);
        code.jp(fallback, code.T_NEAR);
        code.L(end);

        code.SwitchToFarCode();
        code.L(fallback);

        code.sub(rsp, 8);
        ABI_PushCallerSaveRegistersAndAdjustStackExcept(code, HostLocXmmIdx(result.getIdx()));
        code.movq(code.ABI_PARAM1, operand1);
        code.movq(code.ABI_PARAM2, operand2);
        code.mov(code.ABI_PARAM3.cvt32(), ctx.FPCR());
        code.lea(code.ABI_PARAM4, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
        code.CallFunction(&FP::FPRecipStepFused<FPT>);
        code.movq(result, code.ABI_RETURN);
        ABI_PopCallerSaveRegistersAndAdjustStackExcept(code, HostLocXmmIdx(result.getIdx()));
        code.add(rsp, 8);

        code.jmp(end, code.T_NEAR);
        code.SwitchToNearCode();

        ctx.reg_alloc.DefineValue(inst, result);
        return;
    }

    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    ctx.reg_alloc.HostCall(inst, args[0], args[1]);
    code.mov(code.ABI_PARAM3.cvt32(), ctx.FPCR());
    code.lea(code.ABI_PARAM4, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
    code.CallFunction(&FP::FPRecipStepFused<FPT>);
}

void EmitX64::EmitFPRecipStepFused32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRecipStepFused<32>(code, ctx, inst);
}

void EmitX64::EmitFPRecipStepFused64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRecipStepFused<64>(code, ctx, inst);
}

static void EmitFPRound(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst, size_t fsize) {
    const auto rounding = static_cast<FP::RoundingMode>(inst->GetArg(1).GetU8());
    const bool exact = inst->GetArg(2).GetU1();

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tSSE41) && rounding != FP::RoundingMode::ToNearest_TieAwayFromZero && !exact) {
        const int round_imm = [&]{
            switch (rounding) {
            case FP::RoundingMode::ToNearest_TieEven:
                return 0b00;
            case FP::RoundingMode::TowardsPlusInfinity:
                return 0b10;
            case FP::RoundingMode::TowardsMinusInfinity:
                return 0b01;
            case FP::RoundingMode::TowardsZero:
                return 0b11;
            default:
                UNREACHABLE();
            }
            return 0;
        }();

        if (fsize == 64) {
            FPTwoOp<64>(code, ctx, inst, [&](Xbyak::Xmm result) {
                code.roundsd(result, result, round_imm);
            });
        } else {
            FPTwoOp<32>(code, ctx, inst, [&](Xbyak::Xmm result) {
                code.roundss(result, result, round_imm);
            });
        }

        return;
    }

    using fsize_list = mp::list<mp::vlift<size_t(32)>, mp::vlift<size_t(64)>>;
    using rounding_list = mp::list<
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::ToNearest_TieEven>,
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::TowardsPlusInfinity>,
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::TowardsMinusInfinity>,
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::TowardsZero>,
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::ToNearest_TieAwayFromZero>
    >;
    using exact_list = mp::list<mp::vlift<true>, mp::vlift<false>>;

    using key_type = std::tuple<size_t, FP::RoundingMode, bool>;
    using value_type = u64(*)(u64, FP::FPSR&, FP::FPCR);

    static const auto lut = mp::GenerateLookupTableFromList<key_type, value_type>(
        [](auto args) {
            return std::pair<key_type, value_type>{
                mp::to_tuple<decltype(args)>,
                static_cast<value_type>(
                    [](u64 input, FP::FPSR& fpsr, FP::FPCR fpcr) {
                        constexpr auto t = mp::to_tuple<decltype(args)>;
                        constexpr size_t fsize = std::get<0>(t);
                        constexpr FP::RoundingMode rounding_mode = std::get<1>(t);
                        constexpr bool exact = std::get<2>(t);
                        using InputSize = mp::unsigned_integer_of_size<fsize>;

                        return FP::FPRoundInt<InputSize>(static_cast<InputSize>(input), fpcr, rounding_mode, exact, fpsr);
                    }
                )
            };
        },
        mp::cartesian_product<fsize_list, rounding_list, exact_list>{}
    );

    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    ctx.reg_alloc.HostCall(inst, args[0]);
    code.lea(code.ABI_PARAM2, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
    code.mov(code.ABI_PARAM3.cvt32(), ctx.FPCR());
    code.CallFunction(lut.at(std::make_tuple(fsize, rounding, exact)));
}

void EmitX64::EmitFPRoundInt32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRound(code, ctx, inst, 32);
}

void EmitX64::EmitFPRoundInt64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRound(code, ctx, inst, 64);
}

template<typename FPT>
static void EmitFPRSqrtEstimate(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    ctx.reg_alloc.HostCall(inst, args[0]);
    code.mov(code.ABI_PARAM2.cvt32(), ctx.FPCR());
    code.lea(code.ABI_PARAM3, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
    code.CallFunction(&FP::FPRSqrtEstimate<FPT>);
}

void EmitX64::EmitFPRSqrtEstimate32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRSqrtEstimate<u32>(code, ctx, inst);
}

void EmitX64::EmitFPRSqrtEstimate64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRSqrtEstimate<u64>(code, ctx, inst);
}

template<size_t fsize>
static void EmitFPRSqrtStepFused(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst) {
    using FPT = mp::unsigned_integer_of_size<fsize>;

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tFMA) && code.DoesCpuSupport(Xbyak::util::Cpu::tAVX)) {
        auto args = ctx.reg_alloc.GetArgumentInfo(inst);

        Xbyak::Label end, fallback;

        const Xbyak::Xmm operand1 = ctx.reg_alloc.UseXmm(args[0]);
        const Xbyak::Xmm operand2 = ctx.reg_alloc.UseXmm(args[1]);
        const Xbyak::Xmm result = ctx.reg_alloc.ScratchXmm();

        code.vmovaps(result, code.MConst(xword, FP::FPValue<FPT, false, 0, 3>()));
        FCODE(vfnmadd231s)(result, operand1, operand2);

        // Detect if the intermediate result is infinity or NaN or nearly an infinity.
        // Why do we need to care about infinities? This is because x86 doesn't allow us
        // to fuse the divide-by-two with the rest of the FMA operation. Therefore the
        // intermediate value may overflow and we would like to handle this case.
        const Xbyak::Reg32 tmp = ctx.reg_alloc.ScratchGpr().cvt32();
        code.vpextrw(tmp, result, fsize == 32 ? 1 : 3);
        code.and_(tmp.cvt16(), fsize == 32 ? 0x7f80 : 0x7ff0);
        code.cmp(tmp.cvt16(), fsize == 32 ? 0x7f00 : 0x7fe0);
        ctx.reg_alloc.Release(tmp);

        code.jae(fallback, code.T_NEAR);

        FCODE(vmuls)(result, result, code.MConst(xword, FP::FPValue<FPT, false, -1, 1>()));
        code.L(end);

        code.SwitchToFarCode();
        code.L(fallback);

        code.sub(rsp, 8);
        ABI_PushCallerSaveRegistersAndAdjustStackExcept(code, HostLocXmmIdx(result.getIdx()));
        code.movq(code.ABI_PARAM1, operand1);
        code.movq(code.ABI_PARAM2, operand2);
        code.mov(code.ABI_PARAM3.cvt32(), ctx.FPCR());
        code.lea(code.ABI_PARAM4, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
        code.CallFunction(&FP::FPRSqrtStepFused<FPT>);
        code.movq(result, code.ABI_RETURN);
        ABI_PopCallerSaveRegistersAndAdjustStackExcept(code, HostLocXmmIdx(result.getIdx()));
        code.add(rsp, 8);

        code.jmp(end, code.T_NEAR);
        code.SwitchToNearCode();

        ctx.reg_alloc.DefineValue(inst, result);
        return;
    }

    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    ctx.reg_alloc.HostCall(inst, args[0], args[1]);
    code.mov(code.ABI_PARAM3.cvt32(), ctx.FPCR());
    code.lea(code.ABI_PARAM4, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
    code.CallFunction(&FP::FPRSqrtStepFused<FPT>);
}

void EmitX64::EmitFPRSqrtStepFused32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRSqrtStepFused<32>(code, ctx, inst);
}

void EmitX64::EmitFPRSqrtStepFused64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPRSqrtStepFused<64>(code, ctx, inst);
}

void EmitX64::EmitFPSqrt32(EmitContext& ctx, IR::Inst* inst) {
    FPTwoOp<32>(code, ctx, inst, &Xbyak::CodeGenerator::sqrtss);
}

void EmitX64::EmitFPSqrt64(EmitContext& ctx, IR::Inst* inst) {
    FPTwoOp<64>(code, ctx, inst, &Xbyak::CodeGenerator::sqrtsd);
}

void EmitX64::EmitFPSub32(EmitContext& ctx, IR::Inst* inst) {
    FPThreeOp<32>(code, ctx, inst, &Xbyak::CodeGenerator::subss);
}

void EmitX64::EmitFPSub64(EmitContext& ctx, IR::Inst* inst) {
    FPThreeOp<64>(code, ctx, inst, &Xbyak::CodeGenerator::subsd);
}

static Xbyak::Reg64 SetFpscrNzcvFromFlags(BlockOfCode& code, EmitContext& ctx) {
    ctx.reg_alloc.ScratchGpr({HostLoc::RCX}); // shifting requires use of cl
    Xbyak::Reg64 nzcv = ctx.reg_alloc.ScratchGpr();

    //               x64 flags    ARM flags
    //               ZF  PF  CF     NZCV
    // Unordered      1   1   1     0011
    // Greater than   0   0   0     0010
    // Less than      0   0   1     1000
    // Equal          1   0   0     0110
    //
    // Thus we can take use ZF:CF as an index into an array like so:
    //  x64      ARM      ARM as x64
    // ZF:CF     NZCV     NZ-----C-------V
    //   0       0010     0000000100000000 = 0x0100
    //   1       1000     1000000000000000 = 0x8000
    //   2       0110     0100000100000000 = 0x4100
    //   3       0011     0000000100000001 = 0x0101

    code.mov(nzcv, 0x0101'4100'8000'0100);
    code.sete(cl);
    code.rcl(cl, 5); // cl = ZF:CF:0000
    code.shr(nzcv, cl);

    return nzcv;
}

void EmitX64::EmitFPCompare32(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    Xbyak::Xmm reg_a = ctx.reg_alloc.UseXmm(args[0]);
    Xbyak::Xmm reg_b = ctx.reg_alloc.UseXmm(args[1]);
    bool exc_on_qnan = args[2].GetImmediateU1();

    if (exc_on_qnan) {
        code.comiss(reg_a, reg_b);
    } else {
        code.ucomiss(reg_a, reg_b);
    }

    Xbyak::Reg64 nzcv = SetFpscrNzcvFromFlags(code, ctx);
    ctx.reg_alloc.DefineValue(inst, nzcv);
}

void EmitX64::EmitFPCompare64(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    Xbyak::Xmm reg_a = ctx.reg_alloc.UseXmm(args[0]);
    Xbyak::Xmm reg_b = ctx.reg_alloc.UseXmm(args[1]);
    bool exc_on_qnan = args[2].GetImmediateU1();

    if (exc_on_qnan) {
        code.comisd(reg_a, reg_b);
    } else {
        code.ucomisd(reg_a, reg_b);
    }

    Xbyak::Reg64 nzcv = SetFpscrNzcvFromFlags(code, ctx);
    ctx.reg_alloc.DefineValue(inst, nzcv);
}

void EmitX64::EmitFPSingleToDouble(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    const Xbyak::Xmm result = ctx.reg_alloc.UseScratchXmm(args[0]);

    code.cvtss2sd(result, result);
    if (ctx.FPSCR_DN()) {
        ForceToDefaultNaN<64>(code, result);
    }

    ctx.reg_alloc.DefineValue(inst, result);
}

void EmitX64::EmitFPDoubleToSingle(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    const Xbyak::Xmm result = ctx.reg_alloc.UseScratchXmm(args[0]);

    code.cvtsd2ss(result, result);
    if (ctx.FPSCR_DN()) {
        ForceToDefaultNaN<32>(code, result);
    }

    ctx.reg_alloc.DefineValue(inst, result);
}

static void EmitFPToFixed(BlockOfCode& code, EmitContext& ctx, IR::Inst* inst, size_t fsize, bool unsigned_, size_t isize) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const size_t fbits = args[1].GetImmediateU8();
    const auto rounding = static_cast<FP::RoundingMode>(args[2].GetImmediateU8());

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tSSE41) && rounding != FP::RoundingMode::ToNearest_TieAwayFromZero){
        const Xbyak::Xmm src = ctx.reg_alloc.UseScratchXmm(args[0]);

        const int round_imm = [&]{
            switch (rounding) {
            case FP::RoundingMode::ToNearest_TieEven:
            default:
                return 0b00;
            case FP::RoundingMode::TowardsPlusInfinity:
                return 0b10;
            case FP::RoundingMode::TowardsMinusInfinity:
                return 0b01;
            case FP::RoundingMode::TowardsZero:
                return 0b11;
            }
        }();

        const Xbyak::Xmm scratch = ctx.reg_alloc.ScratchXmm();
        const Xbyak::Reg64 result = ctx.reg_alloc.ScratchGpr().cvt64();

        if (fsize == 64) {
            if (fbits != 0) {
                const u64 scale_factor = static_cast<u64>((fbits + 1023) << 52);
                code.mulsd(src, code.MConst(xword, scale_factor));
            }

            code.roundsd(src, src, round_imm);
        } else {
            if (fbits != 0) {
                const u32 scale_factor = static_cast<u32>((fbits + 127) << 23);
                code.mulss(src, code.MConst(xword, scale_factor));
            }

            code.roundss(src, src, round_imm);
            code.cvtss2sd(src, src);
        }

        ZeroIfNaN<64>(code, src, scratch);

        if (isize == 64) {
            Xbyak::Label saturate_max, end;

            if (unsigned_) {
                code.maxsd(src, code.MConst(xword, f64_min_u64));
            }
            code.movsd(scratch, code.MConst(xword, unsigned_ ? f64_max_u64_lim : f64_max_s64_lim));
            code.comisd(scratch, src);
            code.jna(saturate_max, code.T_NEAR);
            if (unsigned_) {
                Xbyak::Label below_max;

                code.movsd(scratch, code.MConst(xword, f64_max_s64_lim));
                code.comisd(src, scratch);
                code.jb(below_max);
                code.subsd(src, scratch);
                code.cvttsd2si(result, src);
                code.btc(result, 63);
                code.jmp(end);
                code.L(below_max);
            }
            code.cvttsd2si(result, src); // 64 bit gpr
            code.L(end);

            code.SwitchToFarCode();
            code.L(saturate_max);
            code.mov(result, unsigned_ ? 0xFFFF'FFFF'FFFF'FFFF : 0x7FFF'FFFF'FFFF'FFFF);
            code.jmp(end, code.T_NEAR);
            code.SwitchToNearCode();
        } else {
            code.minsd(src, code.MConst(xword, unsigned_ ? f64_max_u32 : f64_max_s32));
            if (unsigned_) {
                code.maxsd(src, code.MConst(xword, f64_min_u32));
                code.cvttsd2si(result, src); // 64 bit gpr
            } else {
                code.cvttsd2si(result.cvt32(), src);
            }
        }

        ctx.reg_alloc.DefineValue(inst, result);

        return;
    }

    using fsize_list = mp::list<mp::vlift<size_t(32)>, mp::vlift<size_t(64)>>;
    using unsigned_list = mp::list<mp::vlift<true>, mp::vlift<false>>;
    using isize_list = mp::list<mp::vlift<size_t(32)>, mp::vlift<size_t(64)>>;
    using rounding_list = mp::list<
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::ToNearest_TieEven>,
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::TowardsPlusInfinity>,
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::TowardsMinusInfinity>,
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::TowardsZero>,
        std::integral_constant<FP::RoundingMode, FP::RoundingMode::ToNearest_TieAwayFromZero>
    >;

    using key_type = std::tuple<size_t, bool, size_t, FP::RoundingMode>;
    using value_type = u64(*)(u64, u8, FP::FPSR&, FP::FPCR);

    static const auto lut = mp::GenerateLookupTableFromList<key_type, value_type>(
        [](auto args) {
            return std::pair<key_type, value_type>{
                mp::to_tuple<decltype(args)>,
                static_cast<value_type>(
                    [](u64 input, u8 fbits, FP::FPSR& fpsr, FP::FPCR fpcr) {
                        constexpr auto t = mp::to_tuple<decltype(args)>;
                        constexpr size_t fsize = std::get<0>(t);
                        constexpr bool unsigned_ = std::get<1>(t);
                        constexpr size_t isize = std::get<2>(t);
                        constexpr FP::RoundingMode rounding_mode = std::get<3>(t);
                        using InputSize = mp::unsigned_integer_of_size<fsize>;

                        return FP::FPToFixed<InputSize>(isize, static_cast<InputSize>(input), fbits, unsigned_, fpcr, rounding_mode, fpsr);
                    }
                )
            };
        },
        mp::cartesian_product<fsize_list, unsigned_list, isize_list, rounding_list>{}
    );

    ctx.reg_alloc.HostCall(inst, args[0], args[1]);
    code.lea(code.ABI_PARAM3, code.ptr[code.r15 + code.GetJitStateInfo().offsetof_fpsr_exc]);
    code.mov(code.ABI_PARAM4.cvt32(), ctx.FPCR());
    code.CallFunction(lut.at(std::make_tuple(fsize, unsigned_, isize, rounding)));
}

void EmitX64::EmitFPDoubleToFixedS32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPToFixed(code, ctx, inst, 64, false, 32);
}

void EmitX64::EmitFPDoubleToFixedS64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPToFixed(code, ctx, inst, 64, false, 64);
}

void EmitX64::EmitFPDoubleToFixedU32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPToFixed(code, ctx, inst, 64, true, 32);
}

void EmitX64::EmitFPDoubleToFixedU64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPToFixed(code, ctx, inst, 64, true, 64);
}

void EmitX64::EmitFPSingleToFixedS32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPToFixed(code, ctx, inst, 32, false, 32);
}

void EmitX64::EmitFPSingleToFixedS64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPToFixed(code, ctx, inst, 32, false, 64);
}

void EmitX64::EmitFPSingleToFixedU32(EmitContext& ctx, IR::Inst* inst) {
    EmitFPToFixed(code, ctx, inst, 32, true, 32);
}

void EmitX64::EmitFPSingleToFixedU64(EmitContext& ctx, IR::Inst* inst) {
    EmitFPToFixed(code, ctx, inst, 32, true, 64);
}

void EmitX64::EmitFPS32ToSingle(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    Xbyak::Reg32 from = ctx.reg_alloc.UseGpr(args[0]).cvt32();
    Xbyak::Xmm to = ctx.reg_alloc.ScratchXmm();
    bool round_to_nearest = args[1].GetImmediateU1();
    ASSERT_MSG(!round_to_nearest, "round_to_nearest unimplemented");

    code.cvtsi2ss(to, from);

    ctx.reg_alloc.DefineValue(inst, to);
}

void EmitX64::EmitFPU32ToSingle(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const Xbyak::Xmm to = ctx.reg_alloc.ScratchXmm();
    const bool round_to_nearest = args[1].GetImmediateU1();
    ASSERT_MSG(!round_to_nearest, "round_to_nearest unimplemented");

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tAVX512F)) {
        const Xbyak::Reg64 from = ctx.reg_alloc.UseGpr(args[0]);
        code.vcvtusi2ss(to, to, from.cvt32());
    } else {
        // We are using a 64-bit GPR register to ensure we don't end up treating the input as signed
        const Xbyak::Reg64 from = ctx.reg_alloc.UseScratchGpr(args[0]);
        code.mov(from.cvt32(), from.cvt32()); // TODO: Verify if this is necessary
        code.cvtsi2ss(to, from);
    }

    ctx.reg_alloc.DefineValue(inst, to);
}

void EmitX64::EmitFPS32ToDouble(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);
    Xbyak::Reg32 from = ctx.reg_alloc.UseGpr(args[0]).cvt32();
    Xbyak::Xmm to = ctx.reg_alloc.ScratchXmm();
    bool round_to_nearest = args[1].GetImmediateU1();
    ASSERT_MSG(!round_to_nearest, "round_to_nearest unimplemented");

    code.cvtsi2sd(to, from);

    ctx.reg_alloc.DefineValue(inst, to);
}

void EmitX64::EmitFPS64ToDouble(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const Xbyak::Reg64 from = ctx.reg_alloc.UseGpr(args[0]);
    const Xbyak::Xmm result = ctx.reg_alloc.ScratchXmm();
    const bool round_to_nearest = args[1].GetImmediateU1();
    ASSERT_MSG(!round_to_nearest, "round_to_nearest unimplemented");

    code.cvtsi2sd(result, from);

    ctx.reg_alloc.DefineValue(inst, result);
}

void EmitX64::EmitFPS64ToSingle(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const Xbyak::Reg64 from = ctx.reg_alloc.UseGpr(args[0]);
    const Xbyak::Xmm result = ctx.reg_alloc.ScratchXmm();
    const bool round_to_nearest = args[1].GetImmediateU1();
    ASSERT_MSG(!round_to_nearest, "round_to_nearest unimplemented");

    code.cvtsi2ss(result, from);

    ctx.reg_alloc.DefineValue(inst, result);
}

void EmitX64::EmitFPU32ToDouble(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const Xbyak::Xmm to = ctx.reg_alloc.ScratchXmm();
    const bool round_to_nearest = args[1].GetImmediateU1();
    ASSERT_MSG(!round_to_nearest, "round_to_nearest unimplemented");

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tAVX512F)) {
        const Xbyak::Reg64 from = ctx.reg_alloc.UseGpr(args[0]);
        code.vcvtusi2sd(to, to, from.cvt32());
    } else {
        // We are using a 64-bit GPR register to ensure we don't end up treating the input as signed
        const Xbyak::Reg64 from = ctx.reg_alloc.UseScratchGpr(args[0]);
        code.mov(from.cvt32(), from.cvt32()); // TODO: Verify if this is necessary
        code.cvtsi2sd(to, from);
    }

    ctx.reg_alloc.DefineValue(inst, to);
}

void EmitX64::EmitFPU64ToDouble(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const Xbyak::Reg64 from = ctx.reg_alloc.UseGpr(args[0]);
    const Xbyak::Xmm result = ctx.reg_alloc.ScratchXmm();
    const bool round_to_nearest = args[1].GetImmediateU1();
    ASSERT_MSG(!round_to_nearest, "round_to_nearest unimplemented");

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tAVX512F)) {
        code.vcvtusi2sd(result, result, from);
    } else {
        const Xbyak::Xmm tmp = ctx.reg_alloc.ScratchXmm();

        code.movq(tmp, from);
        code.punpckldq(tmp, code.MConst(xword, 0x4530000043300000, 0));
        code.subpd(tmp, code.MConst(xword, 0x4330000000000000, 0x4530000000000000));
        code.pshufd(result, tmp, 0b01001110);
        code.addpd(result, tmp);
        if (ctx.FPSCR_RMode() == FP::RoundingMode::TowardsMinusInfinity) {
            code.pand(result, code.MConst(xword, f64_non_sign_mask));
        }
    }

    ctx.reg_alloc.DefineValue(inst, result);
}

void EmitX64::EmitFPU64ToSingle(EmitContext& ctx, IR::Inst* inst) {
    auto args = ctx.reg_alloc.GetArgumentInfo(inst);

    const Xbyak::Xmm result = ctx.reg_alloc.ScratchXmm();
    const bool round_to_nearest = args[1].GetImmediateU1();
    ASSERT_MSG(!round_to_nearest, "round_to_nearest unimplemented");

    if (code.DoesCpuSupport(Xbyak::util::Cpu::tAVX512F)) {
        const Xbyak::Reg64 from = ctx.reg_alloc.UseGpr(args[0]);
        code.vcvtusi2ss(result, result, from);
    } else {
        const Xbyak::Reg64 from = ctx.reg_alloc.UseScratchGpr(args[0]);
        code.pxor(result, result);

        Xbyak::Label negative;
        Xbyak::Label end;

        code.test(from, from);
        code.js(negative);

        code.cvtsi2ss(result, from);
        code.jmp(end);

        code.L(negative);
        const Xbyak::Reg64 tmp = ctx.reg_alloc.ScratchGpr();
        code.mov(tmp, from);
        code.shr(tmp, 1);
        code.and_(from.cvt32(), 1);
        code.or_(from, tmp);
        code.cvtsi2ss(result, from);
        code.addss(result, result);

        code.L(end);
    }

    ctx.reg_alloc.DefineValue(inst, result);
}
} // namespace Dynarmic::BackendX64