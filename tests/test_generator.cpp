/* This file is part of the dynarmic project.
 * Copyright (c) 2022 MerryMage
 * SPDX-License-Identifier: 0BSD
 */

#include <array>
#include <string>
#include <tuple>
#include <vector>

#include <dynarmic/common/common_types.h>
#include <dynarmic/frontend/A32/ITState.h>
#include <dynarmic/frontend/A32/a32_location_descriptor.h>
#include <dynarmic/frontend/A32/a32_types.h>
#include <dynarmic/frontend/A32/translate/a32_translate.h>
#include <dynarmic/ir/basic_block.h>
#include <dynarmic/ir/opcodes.h>

#include "A32/testenv.h"
#include "A64/testenv.h"
#include "dynarmic/interface/A64/config.h"
#include "fuzz_util.h"
#include "rand_int.h"

using namespace Dynarmic;

bool ShouldTestInst(u32 instruction, u32 pc, bool is_thumb, bool is_last_inst, A32::ITState it_state = {}) {
    const A32::LocationDescriptor location = A32::LocationDescriptor{pc, {}, {}}.SetTFlag(is_thumb).SetIT(it_state);
    IR::Block block{location};
    const bool should_continue = A32::TranslateSingleInstruction(block, location, instruction);

    if (!should_continue && !is_last_inst) {
        return false;
    }

    if (auto terminal = block.GetTerminal(); boost::get<IR::Term::Interpret>(&terminal)) {
        return false;
    }

    for (const auto& ir_inst : block) {
        switch (ir_inst.GetOpcode()) {
        case IR::Opcode::A32ExceptionRaised:
        case IR::Opcode::A32CallSupervisor:
        case IR::Opcode::A32CoprocInternalOperation:
        case IR::Opcode::A32CoprocSendOneWord:
        case IR::Opcode::A32CoprocSendTwoWords:
        case IR::Opcode::A32CoprocGetOneWord:
        case IR::Opcode::A32CoprocGetTwoWords:
        case IR::Opcode::A32CoprocLoadWords:
        case IR::Opcode::A32CoprocStoreWords:
            return false;
        case IR::Opcode::A32ClearExclusive:
        case IR::Opcode::A32ReadMemory8:
        case IR::Opcode::A32ReadMemory16:
        case IR::Opcode::A32ReadMemory32:
        case IR::Opcode::A32ReadMemory64:
        case IR::Opcode::A32ExclusiveReadMemory8:
        case IR::Opcode::A32ExclusiveReadMemory16:
        case IR::Opcode::A32ExclusiveReadMemory32:
        case IR::Opcode::A32ExclusiveReadMemory64:
        case IR::Opcode::A32WriteMemory8:
        case IR::Opcode::A32WriteMemory16:
        case IR::Opcode::A32WriteMemory32:
        case IR::Opcode::A32WriteMemory64:
        case IR::Opcode::A32ExclusiveWriteMemory8:
        case IR::Opcode::A32ExclusiveWriteMemory16:
        case IR::Opcode::A32ExclusiveWriteMemory32:
        case IR::Opcode::A32ExclusiveWriteMemory64:
            return false;
        case IR::Opcode::A32SetRegister:
            return ir_inst.GetArg(0).GetA32RegRef() != A32::Reg::LR;
        default:
            continue;
        }
    }

    return true;
}

std::vector<u16> GenRandomThumbInst(u32 pc, bool is_last_inst, A32::ITState it_state = {}) {
    static const struct InstructionGeneratorInfo {
        std::vector<InstructionGenerator> generators;
        std::vector<InstructionGenerator> invalid;
    } instructions = [] {
        const std::vector<std::tuple<std::string, const char*>> list{
#define INST(fn, name, bitstring) {#fn, bitstring},
#include "dynarmic/frontend/A32/decoder/thumb16.inc"
#undef INST
        };

        std::vector<InstructionGenerator> generators;
        std::vector<InstructionGenerator> invalid;

        // List of instructions not to test
        static constexpr std::array do_not_test{
            "thumb16_BKPT",
            "thumb16_IT",
            "thumb16_SETEND",
            "thumb16_CPS",
        };

        for (const auto& [fn, bitstring] : list) {
            if (std::find(do_not_test.begin(), do_not_test.end(), fn) != do_not_test.end()) {
                invalid.emplace_back(InstructionGenerator{fn, bitstring});
                continue;
            }
            generators.emplace_back(InstructionGenerator{fn, bitstring});
        }

        return InstructionGeneratorInfo{generators, invalid};
    }();

    while (true) {
        const size_t index = RandInt<size_t>(0, instructions.generators.size() - 1);
        const u32 inst = instructions.generators[index].Generate();

        if (ShouldTestInst(inst, pc, true, is_last_inst, it_state)) {
            return {static_cast<u16>(inst)};
        }
    }
}

auto GenGenRandomThumbInst(std::vector<std::string_view> do_test) {
    const struct InstructionGeneratorInfo {
        std::vector<InstructionGenerator> generators;
        std::vector<InstructionGenerator> invalid;
    } instructions = [&do_test] {
        const std::vector<std::tuple<std::string, const char*>> list{
#define INST(fn, name, bitstring) {#fn, bitstring},
#include "dynarmic/frontend/A32/decoder/thumb16.inc"
#include "dynarmic/frontend/A32/decoder/thumb32.inc"
#undef INST
        };

        std::vector<InstructionGenerator> generators;
        std::vector<InstructionGenerator> invalid;

        for (const auto& [fn, bitstring] : list) {
            if (std::find(do_test.begin(), do_test.end(), fn) != do_test.end()) {
                generators.emplace_back(InstructionGenerator{fn, bitstring});
                continue;
            }
            invalid.emplace_back(InstructionGenerator{fn, bitstring});
        }

        return InstructionGeneratorInfo{generators, invalid};
    }();

    return [=](u32 pc, bool is_last_inst, A32::ITState it_state = {}) -> std::vector<u16> {
        while (true) {
            const size_t index = RandInt<size_t>(0, instructions.generators.size() - 1);
            const u32 inst = instructions.generators[index].Generate();
            const bool is_four_bytes = (inst >> 16) != 0;

            ASSERT(std::find(do_test.begin(), do_test.end(), instructions.generators[index].Name()) != do_test.end());

            // if (std::any_of(instructions.invalid.begin(), instructions.invalid.end(), [inst](const auto& invalid) { return invalid.Match(inst); })) {
            //     continue;
            // }

            if (ShouldTestInst(is_four_bytes ? Common::SwapHalves32(inst) : inst, pc, true, is_last_inst, it_state)) {
                if (is_four_bytes)
                    return {static_cast<u16>(inst >> 16), static_cast<u16>(inst)};
                return {static_cast<u16>(inst)};
            }
        }
    };
}

Dynarmic::A32::UserConfig GetUserConfig(ThumbTestEnv& testenv) {
    Dynarmic::A32::UserConfig user_config;
    user_config.optimizations = no_optimizations;
    user_config.callbacks = &testenv;
    return user_config;
}

void ExecuteTest(std::vector<u16> instructions) {
    const u32 start_address = 0x1000;
    const u32 start_cpsr = (RandInt<u32>(0, 0xF) << 28) | 0x1F0;

    std::array<u32, 16> start_regs{};
    std::generate(start_regs.begin(), start_regs.end(), [] { return RandInt<u32>(0, ~u32(0)); });
    start_regs[14] = 1;
    start_regs[15] = start_address;

    ThumbTestEnv env{};
    Dynarmic::A32::Jit jit{GetUserConfig(env)};

    const u32 num_words_to_initial = start_address / sizeof(u16);

    env.code_mem.resize(num_words_to_initial + instructions.size());
    env.code_mem[0] = ThumbTestEnv::infinite_loop;

    std::copy(instructions.begin(), instructions.end(), env.code_mem.begin() + num_words_to_initial);
    env.PadCodeMem();

    jit.Regs() = start_regs;
    jit.Regs()[14] = 1;
    jit.SetCpsr(start_cpsr);

    env.ticks_left = instructions.size();
    jit.Run();

    fmt::print("new PrecomputedThumbTestCase()\n{{\n");

    fmt::print("    Instructions = new ushort[] {{ ");
    for (u16 inst : instructions) {
        fmt::print("0x{:04x}, ", inst);
    }
    fmt::print("0x{:04x}", ThumbTestEnv::infinite_loop);
    fmt::print(" }},\n");

    fmt::print("    StartRegs = new uint[] {{ ");
    for (int i = 0; i < 15; i++) {
        fmt::print("0x{:08x}, ", start_regs[i]);
    }
    fmt::print("0x{:08x}", start_cpsr);
    fmt::print(" }},\n");

    fmt::print("    FinalRegs = new uint[] {{ ");
    for (int i = 0; i < 15; i++) {
        fmt::print("0x{:08x}, ", jit.Regs()[i]);
    }
    fmt::print("0x{:08x}", jit.Cpsr());
    fmt::print(" }},\n");

    fmt::print("}},\n");
}

void GenerateShortTestCase() {
    std::vector<u16> instructions;

    for (size_t i = 0; i < 1000; i++) {
        const std::vector<u16> inst = GenRandomThumbInst(static_cast<u32>(instructions.size() * sizeof(u16)), false);
        instructions.insert(instructions.end(), inst.begin(), inst.end());
    }

    instructions.push_back(0x4770);  // bx lr

    ExecuteTest(instructions);
}

void GenerateTestCaseWithIT() {
    std::vector<u16> instructions;

    while (instructions.size() < 1000) {
        const size_t instructions_this_pass = RandInt<size_t>(0, 25);

        for (size_t i = 0; i < instructions_this_pass; i++) {
            const std::vector<u16> inst = GenRandomThumbInst(static_cast<u32>(instructions.size() * sizeof(u16)), false);
            instructions.insert(instructions.end(), inst.begin(), inst.end());
        }

        // Emit IT instruction
        A32::ITState it_state = [&] {
            while (true) {
                const u16 imm8 = RandInt<u16>(0, 0xFF);
                if (Common::Bits<0, 3>(imm8) == 0b0000 || Common::Bits<4, 7>(imm8) == 0b1111 || (Common::Bits<4, 7>(imm8) == 0b1110 && Common::BitCount(Common::Bits<0, 3>(imm8)) != 1)) {
                    continue;
                }
                instructions.push_back(0b1011111100000000 | imm8);
                return A32::ITState{static_cast<u8>(imm8)};
            }
        }();

        while (it_state.IsInITBlock()) {
            const std::vector<u16> inst = GenRandomThumbInst(static_cast<u32>(instructions.size() * sizeof(u16)), false, it_state);
            instructions.insert(instructions.end(), inst.begin(), inst.end());
            it_state = it_state.Advance();
        }
    }

    instructions.push_back(0x4770);  // bx lr

    ExecuteTest(instructions);
}

void GenerateIT() {
    std::vector<u16> instructions;

    // Emit IT instruction
    A32::ITState it_state = [&] {
        while (true) {
            const u16 imm8 = RandInt<u16>(0, 0xFF);
            if (Common::Bits<0, 3>(imm8) == 0b0000 || Common::Bits<4, 7>(imm8) == 0b1111 || (Common::Bits<4, 7>(imm8) == 0b1110 && Common::BitCount(Common::Bits<0, 3>(imm8)) != 1)) {
                continue;
            }
            instructions.push_back(0b1011111100000000 | imm8);
            return A32::ITState{static_cast<u8>(imm8)};
        }
    }();

    while (it_state.IsInITBlock()) {
        const std::vector<u16> inst = GenRandomThumbInst(static_cast<u32>(instructions.size() * sizeof(u16)), false, it_state);
        instructions.insert(instructions.end(), inst.begin(), inst.end());
        it_state = it_state.Advance();
    }

    instructions.push_back(0x4770);  // bx lr

    ExecuteTest(instructions);
}

void GenerateTestCaseForInstruction(std::string_view inst_name) {
    auto gen = GenGenRandomThumbInst({inst_name});

    std::vector<u16> instructions;

    for (size_t i = 0; i < 1; i++) {
        const std::vector<u16> inst = gen(static_cast<u32>(instructions.size() * sizeof(u16)), false);
        instructions.insert(instructions.end(), inst.begin(), inst.end());
    }
    instructions.push_back(0x4770);  // bx lr

    ExecuteTest(instructions);
}

void GenTestThumbAluReg() {
    fmt::print("// TST (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_TST_reg");
    fmt::print("// AND (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_AND_reg");
    fmt::print("// BIC (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_BIC_reg");
    fmt::print("// MOV (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_MOV_reg");
    fmt::print("// ORR (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_ORR_reg");
    fmt::print("// MVN (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_MVN_reg");
    fmt::print("// ORN (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_ORN_reg");
    fmt::print("// TEQ (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_TEQ_reg");
    fmt::print("// EOR (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_EOR_reg");
    fmt::print("// CMN (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_CMN_reg");
    fmt::print("// ADD (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_ADD_reg");
    fmt::print("// ADC (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_ADC_reg");
    fmt::print("// SBC (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_SBC_reg");
    fmt::print("// CMP (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_CMP_reg");
    fmt::print("// SUB (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_SUB_reg");
    fmt::print("// RSB (reg)");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_RSB_reg");
}

void GenFcvtTests() {
    std::vector<u64> in32{
        // Special values
        0x0000'0000,  // positive zero
        0x0000'0001,  // smallest positive denormal
        0x0000'1000,
        0x007F'FFFF,  // largest positive denormal
        0x0080'0000,  // smallest positive normal
        0x0080'0002,
        0x3F80'0000,  // 1.0
        0x7F7F'FFFF,  // largest positive normal
        0x7F80'0000,  // positive infinity
        0x7F80'0001,  // first positive SNaN
        0x7FBF'FFFF,  // last positive SNaN
        0x7FC0'0000,  // first positive QNaN
        0x7FFF'FFFF,  // last positive QNaN
        0x8000'0000,  // negative zero
        0x8000'0001,  // smallest negative denormal
        0x8000'1000,
        0x807F'FFFF,  // largest negative denormal
        0x8080'0000,  // smallest negative normal
        0x8080'0002,
        0xBFF0'0000,  // -1.0
        0xFF7F'FFFF,  // largest negative normal
        0xFF80'0000,  // negative infinity
        0xFF80'0001,  // first negative SNaN
        0xFFBF'FFFF,  // last negative SNaN
        0xFFC0'0000,  // first negative QNaN
        0xFFFF'FFFF,  // last negative QNaN

        0x4EFF'FFFD,
        0x4EFF'FFFE,
        0x4EFF'FFFF,
        0x4F00'0000,  // 2147483648
        0x4F00'0001,
        0x4F00'0002,
        0x4F00'0003,

        0xCEFF'FFFD,
        0xCEFF'FFFE,
        0xCEFF'FFFF,
        0xCF00'0000,  // -2147483648
        0xCF00'0001,
        0xCF00'0002,
        0xCF00'0003,

        0x4F7F'FFFD,
        0x4F7F'FFFE,
        0x4F7F'FFFF,
        0x4F80'0000,  // 4294967296
        0x4F80'0001,
        0x4F80'0002,
        0x4F80'0003,

        0xCF7F'FFFD,
        0xCF7F'FFFE,
        0xCF7F'FFFF,
        0xCF80'0000,  // -4294967296
        0xCF80'0001,
        0xCF80'0002,
        0xCF80'0003,

        0x5EFF'FFFD,
        0x5EFF'FFFE,
        0x5EFF'FFFF,
        0x5F00'0000,  // 9223372036854775808
        0x5F00'0001,
        0x5F00'0002,
        0x5F00'0003,

        0xDEFF'FFFD,
        0xDEFF'FFFE,
        0xDEFF'FFFF,
        0xDF00'0000,  // -9223372036854775808
        0xDF00'0001,
        0xDF00'0002,
        0xDF00'0003,

        0x5F7F'FFFD,
        0x5F7F'FFFE,
        0x5F7F'FFFF,
        0x5F80'0000,  // 18446744073709551616
        0x5F80'0001,
        0x5F80'0002,
        0x5F80'0003,

        0xDF7F'FFFD,
        0xDF7F'FFFE,
        0xDF7F'FFFF,
        0xDF80'0000,  // -18446744073709551616
        0xDF80'0001,
        0xDF80'0002,
        0xDF80'0003,

        // Some typical numbers
        0x447A'0000,  // 1000
        0xC040'0000,  // -3
        0x4060'0000,  // 3.5
        0x3FA0'0000,  // 1.25
        0x3FC0'0000,  // 1.5
        0x3FE0'0000,  // 1.75
        0xBFA0'0000,  // -1.25
        0xBFC0'0000,  // -1.5
        0xBFE0'0000,  // -1.75
    };

    std::vector<u64> in64{
        // Special values
        0x0000'0000'0000'0000,  // positive zero
        0x0000'0000'0000'0001,  // smallest positive denormal
        0x0000'0000'0100'0000,
        0x000F'FFFF'FFFF'FFFF,  // largest positive denormal
        0x0010'0000'0000'0000,  // smallest positive normal
        0x0010'0000'0000'0002,
        0x3FF0'0000'0000'0000,  // 1.0
        0x7FEF'FFFF'FFFF'FFFF,  // largest positive normal
        0x7FF0'0000'0000'0000,  // positive infinity
        0x7FF0'0000'0000'0001,  // first positive SNaN
        0x7FF7'FFFF'FFFF'FFFF,  // last positive SNaN
        0x7FF8'0000'0000'0000,  // first positive QNaN
        0x7FFF'FFFF'FFFF'FFFF,  // last positive QNaN
        0x8000'0000'0000'0000,  // negative zero
        0x8000'0000'0000'0001,  // smallest negative denormal
        0x8000'0000'0100'0000,
        0x800F'FFFF'FFFF'FFFF,  // largest negative denormal
        0x8010'0000'0000'0000,  // smallest negative normal
        0x8010'0000'0000'0002,
        0xBFF0'0000'0000'0000,  // -1.0
        0xFFEF'FFFF'FFFF'FFFF,  // largest negative normal
        0xFFF0'0000'0000'0000,  // negative infinity
        0xFFF0'0000'0000'0001,  // first negative SNaN
        0xFFF7'FFFF'FFFF'FFFF,  // last negative SNaN
        0xFFF8'0000'0000'0000,  // first negative QNaN
        0xFFFF'FFFF'FFFF'FFFF,  // last negative QNaN

        0x41DFFFFFFF800000,  // 2147483646
        0x41DFFFFFFFC00000,  // 2147483647
        0x41E0000000000000,  // 2147483648
        0x41E0000000200000,  // 2147483649
        0x41E0000000400000,  // 2147483650

        0xC1DFFFFFFF800000,  // -2147483646
        0xC1DFFFFFFFC00000,  // -2147483647
        0xC1E0000000000000,  // -2147483648
        0xC1E0000000200000,  // -2147483649
        0xC1E0000000400000,  // -2147483650

        0x41EFFFFFFFD00000,  // 4294967294
        0x41EFFFFFFFE00000,  // 4294967295
        0x41F0000000000000,  // 4294967296
        0x41F0000000100000,  // 4294967297
        0x41F0000000200000,  // 4294967298

        0xC1EFFFFFFFD00000,  // -4294967294
        0xC1EFFFFFFFE00000,  // -4294967295
        0xC1F0000000000000,  // -4294967296
        0xC1F0000000100000,  // -4294967297
        0xC1F0000000200000,  // -4294967298

        0x43DFFFFFFFFFFFFE,
        0x43DFFFFFFFFFFFFF,
        0x43E0000000000000,  // 9223372036854775808
        0x43E0000000000001,
        0x43E0000000000002,

        0xC3DFFFFFFFFFFFFE,
        0xC3DFFFFFFFFFFFFF,
        0xC3E0000000000000,  // -9223372036854775808
        0xC3E0000000000001,
        0xC3E0000000000002,

        0x43EFFFFFFFFFFFFE,
        0x43EFFFFFFFFFFFFF,
        0x43F0000000000000,  // 18446744073709551616
        0x43F0000000000001,
        0x43F0000000000002,

        0xC3EFFFFFFFFFFFFE,
        0xC3EFFFFFFFFFFFFF,
        0xC3F0000000000000,  // -18446744073709551616
        0xC3F0000000000001,
        0xC3F0000000000002,

        // Some typical numbers
        0x408F'4000'0000'0000,  // 1000
        0xC008'0000'0000'0000,  // -3
        0x400C'0000'0000'0000,  // 3.5
        0x3FF4'0000'0000'0000,  // 1.25
        0x3FF8'0000'0000'0000,  // 1.5
        0x3FFC'0000'0000'0000,  // 1.75
        0xBFF4'0000'0000'0000,  // -1.25
        0xBFF8'0000'0000'0000,  // -1.5
        0xBFFC'0000'0000'0000,  // -1.75
    };

    auto gen = [&](const char* name, u32 base) {
        fmt::print("// {}\n", name);
        fmt::print("{{\n");
        for (u32 z = 0; z < 2; z++) {
            for (u32 y = 0; y < 2; y++) {
                u32 inst = base | (z << 31) | (y << 22);
                const std::vector<u64>& in_values = y ? in64 : in32;

                fmt::print("From{}To{}Inst = 0x{:08x},\n", y ? 64 : 32, z ? 64 : 32, inst);
                fmt::print("From{}To{}Values = {{", y ? 64 : 32, z ? 64 : 32);

                for (u64 in : in_values) {
                    A64TestEnv env;
                    A64::Jit jit{A64::UserConfig{&env}};

                    env.code_mem_start_address = 0x1000;
                    env.code_mem.emplace_back(inst);
                    env.code_mem.emplace_back(0x14000000);  // B .

                    jit.SetVector(0, {in, 0});
                    jit.SetPC(env.code_mem_start_address);

                    env.ticks_left = 2;
                    jit.Run();

                    if (z) {
                        fmt::print("0x{:016x}, ", jit.GetRegister(0));
                    } else {
                        fmt::print("0x{:08x}, ", jit.GetRegister(0));
                    }
                }

                fmt::print("}},\n");
            }
        }
        fmt::print("}},\n");
    };

    // INST(FCVTNS_float,           "FCVTNS (scalar)",                           "z0011110yy100000000000nnnnnddddd")
    gen("FCVTNS", 0b00011110001000000000000000000000);
    // INST(FCVTNU_float,           "FCVTNU (scalar)",                           "z0011110yy100001000000nnnnnddddd")
    gen("FCVTNU", 0b00011110001000010000000000000000);
    // INST(FCVTAS_float,           "FCVTAS (scalar)",                           "z0011110yy100100000000nnnnnddddd")
    gen("FCVTAS", 0b00011110001001000000000000000000);
    // INST(FCVTAU_float,           "FCVTAU (scalar)",                           "z0011110yy100101000000nnnnnddddd")
    gen("FCVTAU", 0b00011110001001010000000000000000);
    // INST(FCVTPS_float,           "FCVTPS (scalar)",                           "z0011110yy101000000000nnnnnddddd")
    gen("FCVTPS", 0b00011110001010000000000000000000);
    // INST(FCVTPU_float,           "FCVTPU (scalar)",                           "z0011110yy101001000000nnnnnddddd")
    gen("FCVTPU", 0b00011110001010010000000000000000);
    // INST(FCVTMS_float,           "FCVTMS (scalar)",                           "z0011110yy110000000000nnnnnddddd")
    gen("FCVTMS", 0b00011110001100000000000000000000);
    // INST(FCVTMU_float,           "FCVTMU (scalar)",                           "z0011110yy110001000000nnnnnddddd")
    gen("FCVTMU", 0b00011110001100010000000000000000);
    // INST(FCVTZS_float_int,       "FCVTZS (scalar, integer)",                  "z0011110yy111000000000nnnnnddddd")
    gen("FCVTZS", 0b00011110001110000000000000000000);
    // INST(FCVTZU_float_int,       "FCVTZU (scalar, integer)",                  "z0011110yy111001000000nnnnnddddd")
    gen("FCVTZU", 0b00011110001110010000000000000000);
}

void GenTestThumbAluImm() {
    fmt::print("// TST (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_TST_imm");
    fmt::print("// AND (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_AND_imm");
    fmt::print("// BIC (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_BIC_imm");
    fmt::print("// MOV (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_MOV_imm");
    fmt::print("// ORR (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_ORR_imm");
    fmt::print("// MVN (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_MVN_imm");
    fmt::print("// ORN (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_ORN_imm");
    fmt::print("// TEQ (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_TEQ_imm");
    fmt::print("// EOR (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_EOR_imm");
    fmt::print("// CMN (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_CMN_imm");
    fmt::print("// ADD (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_ADD_imm_1");
    fmt::print("// ADC (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_ADC_imm");
    fmt::print("// SBC (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_SBC_imm");
    fmt::print("// CMP (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_CMP_imm");
    fmt::print("// SUB (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_SUB_imm_1");
    fmt::print("// RSB (imm)\n");
    for (int i = 0; i < 5; i++)
        GenerateTestCaseForInstruction("thumb32_RSB_imm");
}

void ExecuteMemoryTest(std::vector<u16> instructions, ) {
    const u32 start_address = 0x1000;
    const u32 start_cpsr = (RandInt<u32>(0, 0xF) << 28) | 0x1F0;

    std::array<u32, 16> start_regs{};
    std::generate(start_regs.begin(), start_regs.end(), [] { return RandInt<u32>(0, ~u32(0)); });
    start_regs[14] = 1;
    start_regs[15] = start_address;

    ThumbTestEnv env{};
    Dynarmic::A32::Jit jit{GetUserConfig(env)};

    for (u64 vaddr = 0x2000; vaddr < 0x3000; vaddr += 2) {
        env.MemoryWrite16(vaddr, (u16)vaddr);
    }

    const u32 num_words_to_initial = start_address / sizeof(u16);

    env.code_mem.resize(num_words_to_initial + instructions.size());
    env.code_mem[0] = ThumbTestEnv::infinite_loop;

    std::copy(instructions.begin(), instructions.end(), env.code_mem.begin() + num_words_to_initial);
    env.PadCodeMem();

    jit.Regs() = start_regs;
    jit.Regs()[14] = 1;
    jit.SetCpsr(start_cpsr);

    env.ticks_left = instructions.size();
    jit.Run();

    fmt::print("new PrecomputedMemoryThumbTestCase()\n{{\n");

    fmt::print("    Instructions = new ushort[] {{ ");
    for (u16 inst : instructions) {
        fmt::print("0x{:04x}, ", inst);
    }
    fmt::print("0x{:04x}", ThumbTestEnv::infinite_loop);
    fmt::print(" }},\n");

    fmt::print("    StartRegs = new uint[] {{ ");
    for (int i = 0; i < 15; i++) {
        fmt::print("0x{:08x}, ", start_regs[i]);
    }
    fmt::print("0x{:08x}", start_cpsr);
    fmt::print(" }},\n");

    fmt::print("    FinalRegs = new uint[] {{ ");
    for (int i = 0; i < 15; i++) {
        fmt::print("0x{:08x}, ", jit.Regs()[i]);
    }
    fmt::print("0x{:08x}", jit.Cpsr());
    fmt::print(" }},\n");

    fmt::print("    MemoryDelta = new Tuple<ulong, ushort>{} {{ ");
    for (u64 vaddr = 0x2000; vaddr < 0x3000; vaddr += 2) {
        u16 value = env.MemoryRead16(vaddr);
        u16 expect = (u16)vaddr;
        if (value != expect) {
            fmt::print("new Tuple<ulong, ushort>(0x{:04x}, 0x{:04x}), ", vaddr, value);
        }
    }
    fmt::print(" }},\n");

    fmt::print("}},\n");
}

void GenTestThumbMemImm() {

}

int main(int, char**) {
    GenTestThumbAluImm();
    return 0;
}
