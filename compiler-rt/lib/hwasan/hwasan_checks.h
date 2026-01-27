//===-- hwasan_checks.h -----------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file is a part of HWAddressSanitizer.
//
//===----------------------------------------------------------------------===//

#ifndef HWASAN_CHECKS_H
#define HWASAN_CHECKS_H

#include "hwasan_allocator.h"
#include "hwasan_mapping.h"
#include "hwasan_registers.h"
#include "sanitizer_common/sanitizer_common.h"

// #ifdef CAN_SANITIZE_LEAKS
// #  define CAN_SANITIZE_LEAKS 0
// #endif

namespace __hwasan {

enum class ErrorAction { Abort, Recover };
enum class AccessType { Load, Store };

// Used when the access size is known.
constexpr unsigned SigTrapEncoding(ErrorAction EA, AccessType AT,
                                   unsigned LogSize) {
  return 0x20 * (EA == ErrorAction::Recover) +
         0x10 * (AT == AccessType::Store) + LogSize;
}

// Used when the access size varies at runtime.
constexpr unsigned SigTrapEncoding(ErrorAction EA, AccessType AT) {
  return SigTrapEncoding(EA, AT, 0xf);
}

template <ErrorAction EA, AccessType AT, size_t LogSize>
__attribute__((always_inline)) static void SigTrap(uptr p) {
  // Other platforms like linux can use signals for intercepting an exception
  // and dispatching to HandleTagMismatch. The fuchsias implementation doesn't
  // use signals so we can call it here directly instead.
#if CAN_GET_REGISTERS && SANITIZER_FUCHSIA
  auto regs = GetRegisters();
  size_t size = 2 << LogSize;
  AccessInfo access_info = {
      .addr = p,
      .size = size,
      .is_store = AT == AccessType::Store,
      .is_load = AT == AccessType::Load,
      .recover = EA == ErrorAction::Recover,
  };
  HandleTagMismatch(access_info, (uptr)__builtin_return_address(0),
                    (uptr)__builtin_frame_address(0), /*uc=*/nullptr, regs.x);
#elif defined(__aarch64__)
  (void)p;
  // 0x900 is added to do not interfere with the kernel use of lower values of
  // brk immediate.
  register uptr x0 asm("x0") = p;
  asm("brk %1\n\t" ::"r"(x0), "n"(0x900 + SigTrapEncoding(EA, AT, LogSize)));
#elif defined(__x86_64__)
  // INT3 + NOP DWORD ptr [EAX + X] to pass X to our signal handler, 5 bytes
  // total. The pointer is passed via rdi.
  // 0x40 is added as a safeguard, to help distinguish our trap from others and
  // to avoid 0 offsets in the command (otherwise it'll be reduced to a
  // different nop command, the three bytes one).
  asm volatile(
      "int3\n"
      "nopl %c0(%%rax)\n" ::"n"(0x40 + SigTrapEncoding(EA, AT, LogSize)),
      "D"(p));
#elif SANITIZER_RISCV64
  // Put pointer into x10
  // addiw contains immediate of 0x40 + X, where 0x40 is magic number and X
  // encodes access size
  register uptr x10 asm("x10") = p;
  asm volatile(
      "ebreak\n"
      "addiw x0, x0, %1\n" ::"r"(x10),
      "I"(0x40 + SigTrapEncoding(EA, AT, LogSize)));
#else
  // FIXME: not always sigill.
  __builtin_trap();
#endif
  // __builtin_unreachable();
}

// Version with access size which is not power of 2
template <ErrorAction EA, AccessType AT>
__attribute__((always_inline)) static void SigTrap(uptr p, uptr size) {
  // Other platforms like linux can use signals for intercepting an exception
  // and dispatching to HandleTagMismatch. The fuchsias implementation doesn't
  // use signals so we can call it here directly instead.
#if CAN_GET_REGISTERS && SANITIZER_FUCHSIA
  auto regs = GetRegisters();
  AccessInfo access_info = {
      .addr = p,
      .size = size,
      .is_store = AT == AccessType::Store,
      .is_load = AT == AccessType::Load,
      .recover = EA == ErrorAction::Recover,
  };
  HandleTagMismatch(access_info, (uptr)__builtin_return_address(0),
                    (uptr)__builtin_frame_address(0), /*uc=*/nullptr, regs.x);
#elif defined(__aarch64__)
  register uptr x0 asm("x0") = p;
  register uptr x1 asm("x1") = size;
  asm("brk %2\n\t" ::"r"(x0), "r"(x1), "n"(0x900 + SigTrapEncoding(EA, AT)));
#elif defined(__x86_64__)
  // Size is stored in rsi.
  asm volatile(
      "int3\n"
      "nopl %c0(%%rax)\n" ::"n"(0x40 + SigTrapEncoding(EA, AT)),
      "D"(p), "S"(size));
#elif SANITIZER_RISCV64
  // Put access size into x11
  register uptr x10 asm("x10") = p;
  register uptr x11 asm("x11") = size;
  asm volatile(
      "ebreak\n"
      "addiw x0, x0, %2\n" ::"r"(x10),
      "r"(x11), "I"(0x40 + SigTrapEncoding(EA, AT)));
#else
  __builtin_trap();
#endif
  // __builtin_unreachable();
}

__attribute__((always_inline, nodebug)) static inline uptr ShortTagSize(
    tag_t mem_tag, uptr ptr) {
  DCHECK(IsAligned(ptr, kShadowAlignment));
  tag_t ptr_tag = GetTagFromPointer(ptr);
  if (ptr_tag == mem_tag)
    return kShadowAlignment;
  if (!mem_tag || mem_tag >= kShadowAlignment)
    return 0;
  if (*(u8*)(ptr | (kShadowAlignment - 1)) != ptr_tag)
    return 0;
  return mem_tag;
}

__attribute__((always_inline, nodebug)) static inline bool
PossiblyShortTagMatches(tag_t mem_tag, uptr ptr, uptr sz) {
  tag_t ptr_tag = GetTagFromPointer(ptr);
  if (ptr_tag == mem_tag)
    return true;
  if (mem_tag >= kShadowAlignment)
    return false;
  if ((ptr & (kShadowAlignment - 1)) + sz > mem_tag)
    return false;
  return *(u8*)(ptr | (kShadowAlignment - 1)) == ptr_tag;
}

#define getT(tag) (tag & 0b00001111UL)
#define getL(tag) (tag & 0b00110000UL) >> 4
#define getR(tag) (tag & 0b01000000UL) >> 6

template <ErrorAction EA, AccessType AT>
__attribute__((always_inline, nodebug)) static void CheckAddressSized(uptr p,
                                                                      uptr sz) {
  if (sz == 0 || !InTaggableRegion(p)) {
    // VPrintf(1, "[FieldArmor] CAS A=%p S=%u: <SKIP> \n", (void*)p, sz);
    return;
  }

  unsigned char* untagged_ptr = (unsigned char*)(p & ~kAddressTagMask);
  tag_t ptr_tag = GetTagFromPointer(p);
  if (ptr_tag == 0) {
    // atomic_fetch_add(&checks_on_untagged_ptr, 1ULL, memory_order_relaxed);
    return;
  }
  tag_t R = getR(ptr_tag);
  tag_t L = getL(ptr_tag);
  tag_t T = getT(ptr_tag);

  // VPrintf(1, "[FieldArmor] CAS A=%p SZ=%u - PTR R=%u L=%u T=%u\n", (void*)p,
  // sz,
  //         R, L, T);
  tag_t mem_tag = *(tag_t*)MemToShadow((uptr)untagged_ptr);
  if (mem_tag == 0) {
    // atomic_fetch_add(&checks_on_uninited_shadow, 1ULL, memory_order_relaxed);
    return;
  }
  // atomic_fetch_add(&total_checks, 1ULL, memory_order_relaxed);
  // if(atomic_load(&total_checks, memory_order_relaxed) == 0){
  //   // prevent overflow
  //   atomic_store(&overflows, 1ULL, memory_order_relaxed);
  // }

  if (R) {
    // VPrintf(1, "\t\t[FieldArmor] RP CHECK A=%p SZ=%u\n", (void*)p, sz);
    if ((L == 0) && (T == 0))
      return; /* pointer to outer root struct can do whatever -> CASE1*/
    // TODO
  } else {  // R == 0
    // VPrintf(1, "\t[FieldArmor] NO RP CHK A=%p SZ=%u\n", (void*)p, sz);

    for (uptr i = 0; i < sz; i++) {
      mem_tag = *(tag_t*)MemToShadow((uptr)untagged_ptr + i);
      // NOTE: memtag can become 0 at some point if a) going out of bounds on
      // the current object b) flexible array member. We tolerate a), but have
      // to be lenient on b)

      // TODO: un-ignore levels!!!!
      if ((getT(mem_tag)) != getT(ptr_tag) && mem_tag != 0) {
        VPrintf(1, "[FieldArmor] TAG MISMATCH A=%p SZ=%u\n",
                (void*)(untagged_ptr + i), sz);
        VPrintf(1, "\t[FieldArmor] memory T: %u, pointer T: %u\n",
                getT(mem_tag), getT(ptr_tag));
        // VPrintf(1, "\t[FieldArmor] EXP_T=%x, MEM_T=%x\n", ptr_tag,
        // *curr_memtag);

        SigTrap<EA, AT>(p, sz);  // keeps on failing...
        if (EA == ErrorAction::Abort)
          __builtin_unreachable();
      }
      // else VPrintf(1, "\t\t[FieldArmor] TAG MATCH A=%p SZ=%u\n",
      //         (void*)(untagged_ptr+ i), 1);
    }  // for
  }  // NON RP chk
}  // CheckAddressSized

template <ErrorAction EA, AccessType AT, unsigned LogSize>
__attribute__((always_inline, nodebug)) static void CheckAddress(uptr p) {
  if (!InTaggableRegion(p))
    return;
  // VPrintf(1, "[FieldArmor] CA -> A=%p SZ=%u\n", (void*)p, 1 << LogSize);
  // VPrintf(1, "\t[FieldArmor] CALL CAS A=%p SZ=%u\n", (void*)p, 1 << LogSize);
  CheckAddressSized<EA, AT>(p, 1 << LogSize);
}

}  // end namespace __hwasan

#endif  // HWASAN_CHECKS_H
