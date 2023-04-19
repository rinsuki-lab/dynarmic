/* This file is part of the dynarmic project.
 * Copyright (c) 2022 MerryMage
 * SPDX-License-Identifier: 0BSD
 */

#include <oaknut/code_block.hpp>
#include <oaknut/oaknut.hpp>

#include "dynarmic/backend/arm64/abi.h"
#include "dynarmic/common/spin_lock.h"

namespace Dynarmic {

using Backend::Arm64::Wscratch0;
using Backend::Arm64::Wscratch1;
using namespace oaknut::util;

void EmitSpinLockLock(oaknut::CodeGenerator& code, oaknut::XReg ptr) {
    oaknut::Label start, loop;

    code.MOV(Wscratch1, 1);
    code.SEVL();
    code.l(start);
    code.WFE();
    code.l(loop);
    code.LDAXR(Wscratch0, ptr);
    code.CBNZ(Wscratch0, start);
    code.STXR(Wscratch0, Wscratch1, ptr);
    code.CBNZ(Wscratch0, loop);
}

void EmitSpinLockUnlock(oaknut::CodeGenerator& code, oaknut::XReg ptr) {
    code.STLR(WZR, ptr);
}

namespace {

struct SpinLockImpl {
    SpinLockImpl();

    oaknut::CodeBlock mem;
    oaknut::CodeGenerator code;
    void (*lock)(volatile int*);
    void (*unlock)(volatile int*);
};

SpinLockImpl* impl;

SpinLockImpl::SpinLockImpl()
        : mem{4096}
        , code{mem.ptr()} {
    mem.unprotect();

    lock = code.ptr<void (*)(volatile int*)>();
    EmitSpinLockLock(code, X0);
    code.RET();

    unlock = code.ptr<void (*)(volatile int*)>();
    EmitSpinLockUnlock(code, X0);
    code.RET();

    mem.protect();
}

}  // namespace

void SpinLock::Lock() {
    if (__builtin_expect(impl == nullptr, 0)) {
        impl = new SpinLockImpl();
    }
    impl->lock(&storage);
}

void SpinLock::Unlock() {
    if (__builtin_expect(impl == nullptr, 0)) {
        impl = new SpinLockImpl();
    }
    impl->unlock(&storage);
}

}  // namespace Dynarmic
