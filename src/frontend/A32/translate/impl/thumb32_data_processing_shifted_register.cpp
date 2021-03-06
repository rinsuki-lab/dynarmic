/* This file is part of the dynarmic project.
 * Copyright (c) 2016 MerryMage
 * SPDX-License-Identifier: 0BSD
 */

#include "frontend/A32/translate/impl/translate_thumb.h"

namespace Dynarmic::A32 {

bool ThumbTranslatorVisitor::thumb32_TST_reg(Reg n, Imm<3> imm3, Imm<2> imm2, ShiftType type, Reg m) {
    if (n == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto shifted = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag());
    const auto result = ir.And(ir.GetRegister(n), shifted.result);

    ir.SetNFlag(ir.MostSignificantBit(result));
    ir.SetZFlag(ir.IsZero(result));
    ir.SetCFlag(shifted.carry);
    return true;
}

bool ThumbTranslatorVisitor::thumb32_AND_reg(bool S, Reg n, Imm<3> imm3, Reg d, Imm<2> imm2, ShiftType type, Reg m) {
    ASSERT_MSG(!(d == Reg::PC && S), "Decode error");

    if ((d == Reg::PC && !S) || n == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto shifted = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag());
    const auto result = ir.And(ir.GetRegister(n), shifted.result);
    ir.SetRegister(d, result);
    if (S) {
        ir.SetNFlag(ir.MostSignificantBit(result));
        ir.SetZFlag(ir.IsZero(result));
        ir.SetCFlag(shifted.carry);
    }
    return true;
}

bool ThumbTranslatorVisitor::thumb32_BIC_reg(bool S, Reg n, Imm<3> imm3, Reg d, Imm<2> imm2, ShiftType type, Reg m) {
    if (d == Reg::PC || n == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto shifted = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag());
    const auto result = ir.And(ir.GetRegister(n), ir.Not(shifted.result));
    ir.SetRegister(d, result);
    if (S) {
        ir.SetNFlag(ir.MostSignificantBit(result));
        ir.SetZFlag(ir.IsZero(result));
        ir.SetCFlag(shifted.carry);
    }
    return true;
}

bool ThumbTranslatorVisitor::thumb32_MOV_reg(bool S, Imm<3> imm3, Reg d, Imm<2> imm2, ShiftType type, Reg m) {
    if (d == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto shifted = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag());
    const auto result = shifted.result;
    ir.SetRegister(d, result);
    if (S) {
        ir.SetNFlag(ir.MostSignificantBit(result));
        ir.SetZFlag(ir.IsZero(result));
        ir.SetCFlag(shifted.carry);
    }
    return true;
}

bool ThumbTranslatorVisitor::thumb32_ORR_reg(bool S, Reg n, Imm<3> imm3, Reg d, Imm<2> imm2, ShiftType type, Reg m) {
    ASSERT_MSG(n != Reg::PC, "Decode error");

    if (d == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto shifted = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag());
    const auto result = ir.Or(ir.GetRegister(n), shifted.result);
    ir.SetRegister(d, result);
    if (S) {
        ir.SetNFlag(ir.MostSignificantBit(result));
        ir.SetZFlag(ir.IsZero(result));
        ir.SetCFlag(shifted.carry);
    }
    return true;
}

bool ThumbTranslatorVisitor::thumb32_MVN_reg(bool S, Imm<3> imm3, Reg d, Imm<2> imm2, ShiftType type, Reg m) {
    if (d == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto shifted = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag());
    const auto result = ir.Not(shifted.result);
    ir.SetRegister(d, result);
    if (S) {
        ir.SetNFlag(ir.MostSignificantBit(result));
        ir.SetZFlag(ir.IsZero(result));
        ir.SetCFlag(shifted.carry);
    }
    return true;
}

bool ThumbTranslatorVisitor::thumb32_ORN_reg(bool S, Reg n, Imm<3> imm3, Reg d, Imm<2> imm2, ShiftType type, Reg m) {
    ASSERT_MSG(n != Reg::PC, "Decode error");

    if (d == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto shifted = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag());
    const auto result = ir.Or(ir.GetRegister(n), ir.Not(shifted.result));
    ir.SetRegister(d, result);
    if (S) {
        ir.SetNFlag(ir.MostSignificantBit(result));
        ir.SetZFlag(ir.IsZero(result));
        ir.SetCFlag(shifted.carry);
    }
    return true;
}

bool ThumbTranslatorVisitor::thumb32_TEQ_reg(Reg n, Imm<3> imm3, Imm<2> imm2, ShiftType type, Reg m) {
    if (n == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto shifted = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag());
    const auto result = ir.Eor(ir.GetRegister(n), shifted.result);

    ir.SetNFlag(ir.MostSignificantBit(result));
    ir.SetZFlag(ir.IsZero(result));
    ir.SetCFlag(shifted.carry);
    return true;
}

bool ThumbTranslatorVisitor::thumb32_EOR_reg(bool S, Reg n, Imm<3> imm3, Reg d, Imm<2> imm2, ShiftType type, Reg m) {
    ASSERT_MSG(!(d == Reg::PC && S), "Decode error");

    if ((d == Reg::PC && !S) || n == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto shifted = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag());
    const auto result = ir.Eor(ir.GetRegister(n), shifted.result);
    ir.SetRegister(d, result);
    if (S) {
        ir.SetNFlag(ir.MostSignificantBit(result));
        ir.SetZFlag(ir.IsZero(result));
        ir.SetCFlag(shifted.carry);
    }
    return true;
}

bool ThumbTranslatorVisitor::thumb32_PKH(Reg n, Imm<3> imm3, Reg d, Imm<2> imm2, Imm<1> tb, Reg m) {
    const ShiftType type = concatenate(tb, Imm<1>{0}).ZeroExtend<ShiftType>();

    if (d == Reg::PC || n == Reg::PC || m == Reg::PC) {
        return UnpredictableInstruction();
    }

    const auto operand2 = EmitImmShift(ir.GetRegister(m), type, imm3, imm2, ir.GetCFlag()).result;
    const auto lower = ir.And((tb == 1) ? operand2 : ir.GetRegister(n), ir.Imm32(0x0000FFFF));
    const auto upper = ir.And((tb == 1) ? ir.GetRegister(n) : operand2, ir.Imm32(0xFFFF0000));
    const auto result = ir.Or(upper, lower);
    ir.SetRegister(d, result);
    return true;
}

} // namespace Dynarmic::A32