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

#include "hwasan/hwasan.h"
#include "hwasan_allocator.h"
#include "hwasan_mapping.h"
#include "hwasan_registers.h"
#include "sanitizer_common/sanitizer_common.h"
#include "sanitizer_common/sanitizer_internal_defs.h"

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

// NOTE: same number of bits for both ARM and x86
#define TAG_BITS 6  // TOTAL number of bits used for tagging

#define getT(tag)                    \
  (tag & ((1ULL << (TAG_BITS - 1)) - \
          1))  // AND-mask to retrieve the T bits, without the R bit
#define getR(tag) ((tag) >> (TAG_BITS - 1))  // retrieve the R bit

// AND-mask preserving ALL TAG bits -> NOTE: this is no longer necessary, here
// just for reference (stale)
#define PTR_TAG_MASK ((1ULL << (TAG_BITS)) - 1)
#define MEM_TAG_MASK \
  ((1ULL << (8ULL)) - 1)  //  SHADOW MEMORY is byte granular. To detect padding
                          //  bytes accesses we must also check the bits that
                          //  are not used for tagging pointers (top 2).

// PADDING BYTES carry this tag. It cannot clash with any tag because
// PADDING_BYTE is 0xff and the maximum tag value is 0x3f (6 bits).
#define PADDING_BYTE 0xff  // just for reference

template <ErrorAction EA, AccessType AT>
__attribute__((always_inline, nodebug)) static void CheckAddressSized(uptr p,
                                                                      uptr sz) {
  if (sz == 0)
    return;
  unsigned char* untagged_ptr = (unsigned char*)(p & ~kAddressTagMask);
  tag_t ptr_tag = GetTagFromPointer(p);
  // when ptr tag is 0, we skip checks

  if (UNLIKELY(ptr_tag == 0)) {
#ifdef PERFORMANCE_DEBUGGING
    atomic_fetch_add(&checks_on_untagged_ptr, 1ULL, memory_order_relaxed);
    if (atomic_load(&checks_on_untagged_ptr, memory_order_relaxed) == 0) {
      // overflow detected
      atomic_fetch_add(&overflows_on_untagged_ptr_checks, 1ULL,
                       memory_order_relaxed);
    }
#endif

    return;
  }  // ptr tag is 0

  uptr baseShadow = MemToShadow((uptr)untagged_ptr);
  uint8_t mem_tag = *((uint8_t*)baseShadow);
  bool memIsNull = (mem_tag) == 0;
  // NOTE: do check on first byte, catch the smallest read possible
  if (UNLIKELY(memIsNull)) {
#ifdef PERFORMANCE_DEBUGGING
    atomic_fetch_add(&checks_on_uninited_shadow, 1ULL, memory_order_relaxed);
    if (atomic_load(&checks_on_uninited_shadow, memory_order_relaxed) == 0) {
      // overflow detected
      atomic_fetch_add(&overflows_on_uninited_shadow_checks, 1ULL,
                       memory_order_relaxed);
    }
#endif
    // check that ALL the bytes in the access are zero. If not, raise error.
    for (unsigned int i = 0; i < sz; i++) {
      uint8_t ShadowTagByte = *(uint8_t*)(baseShadow + i);
      if (UNLIKELY(ShadowTagByte != 0)) {
        VPrintf(
            0, "[check-null] Tag mismatch detected at address %p: ptr "
               "tag=%02x mem tag=%02x\n",
            (void*)(p + i), ptr_tag, ShadowTagByte);
        SigTrap<EA, AT>(p, sz);
      }
    }
    return;
  }  // memtag is 0

  if (getR(ptr_tag) != 0)
    // NOTE: mem* intrinsics call over pointers with R set are no-ops in this
    // design. This removes FPs, at the price of NOT catching some bugs over
    // base pointers to structs.
    return;

  // vectorize check as much as possible
  unsigned int chunks8B = sz / 8;
  unsigned int remainder = sz % 8;

  uint64_t extension_mask = 0x0101010101010101ULL;
  uint64_t ptr_T_8B = ptr_tag * (extension_mask);
  uint64_t mem_T_8B = -1LL;

  for (unsigned int i = 0; i < chunks8B; i++) {
    mem_T_8B = (*(uint64_t*)(baseShadow + i * 8));

    if (UNLIKELY((mem_T_8B != ptr_T_8B))) {
      VPrintf(0, "[CAS-8B] TAG MISMATCH at %p: ptr tag=%016lx mem tag=%016lx\n",
              (void*)(p + i * 8), ptr_T_8B, mem_T_8B);
      SigTrap<EA, AT>(p, sz);
      if (EA == ErrorAction::Abort)
        __builtin_unreachable();
    }
  }  // for

  // BYTE-granular tail checks
  uint64_t ptr_T_B = ptr_tag;
  uptr curShadow = baseShadow + chunks8B * 8;
  for (unsigned int i = 0; i < remainder; i++) {
    tag_t mem_T_B = (*(tag_t*)(curShadow + i));
    if (UNLIKELY((mem_T_B != ptr_T_B))) {
      VPrintf(0, "[CAS-B] TAG MISMATCH at %p: ptr tag=%016lx mem tag=%016lx\n",
              (void*)(p + i), ptr_T_B, mem_T_B);
      SigTrap<EA, AT>(p, sz);
      if (EA == ErrorAction::Abort)
        __builtin_unreachable();
    }
  }  // for

#ifdef PERFORMANCE_DEBUGGING
  atomic_fetch_add(&total_checks, 1ULL, memory_order_relaxed);
  if (atomic_load(&total_checks, memory_order_relaxed) == 0) {
    // overflow detected
    atomic_fetch_add(&overflows_on_total_checks, 1ULL, memory_order_relaxed);
  }
#endif
}  // CheckAddressSized

template <ErrorAction EA, AccessType AT, unsigned LogSize>
__attribute__((always_inline, nodebug)) static void CheckAddress(uptr p) {
  uint8_t tag = GetTagFromPointer(p);
  uptr untagged_ptr = UntagAddr(p);
  uptr shadow_addr = MemToShadow(untagged_ptr);
  uint8_t ShadowTag = (*(uint8_t*)shadow_addr);

  // DEBUG
  if (UNLIKELY(GetTagFromPointer(p) == 0)) {
    return;
  }

  if (UNLIKELY(ShadowTag == 0)) {
    // VPrintf(2, "[CheckAddress] uninited shadow detected at address %p\n",
    // (void*)p); atomic_fetch_add(&checks_on_uninited_shadow, 1ULL,
    // memory_order_relaxed);

    // if (atomic_load(&checks_on_uninited_shadow, memory_order_relaxed) == 0) {
    //   // overflow detected
    //   atomic_fetch_add(&overflows_on_uninited_shadow_checks, 1ULL,
    //                    memory_order_relaxed);
    // }
    // check that ALL the bytes in the access are zero. If not, raise error.

    for (unsigned int i = 0; i < (1 << LogSize); i++) {
      uint8_t ShadowTagByte = *(uint8_t*)(shadow_addr + i);
      if (UNLIKELY(ShadowTagByte != 0)) {
        VPrintf(0,
                "[check-null] Tag mismatch detected at address %p: ptr "
                "tag=%02x mem tag=%02x\n",
                (void*)p, tag, ShadowTagByte);
        SigTrap<EA, AT, LogSize>(p);
      }
    }
    return;
  }

  uint8_t ShadowTagByte = *(uint8_t*)shadow_addr;
  uint8_t PtrTagByte = tag;

  uint16_t PtrTagShort = 0;
  uint16_t ShadowTagShort = 0;

  uint32_t PtrTagInt = 0;
  uint32_t ShadowTagInt = 0;

  uint64_t PtrTagLong = 0;
  uint64_t ShadowTagLong = 0;
  switch (LogSize) {
    case 0: /*byte*/
      ShadowTagByte = *(uint8_t*)shadow_addr;
      PtrTagByte = tag;
      if (UNLIKELY(PtrTagByte != ShadowTagByte)) {
        VPrintf(0,
                "[CHK-B] Tag mismatch detected at address %p: ptr tag=%02x mem "
                "tag=%02x\n",
                (void*)p, PtrTagByte, ShadowTagByte);
        SigTrap<EA, AT, LogSize>(p);
      }
      break;
    case 1: /*2 bytes*/
      PtrTagShort = PtrTagByte * 0x0101U;
      ShadowTagShort = *(uint16_t*)shadow_addr;
      if (UNLIKELY((PtrTagShort != ShadowTagShort))) {
        VPrintf(0,
                "[CHK-S] Tag mismatch detected at address %p: ptr tag=%04x mem "
                "tag=%04x\n",
                (void*)p, PtrTagShort, ShadowTagShort);
        SigTrap<EA, AT, LogSize>(p);
      }
      break;

    case 2: /*4 bytes*/
      PtrTagInt = PtrTagByte * 0x01010101U;
      ShadowTagInt = *(uint32_t*)shadow_addr;
      if (UNLIKELY(PtrTagInt != ShadowTagInt)) {
        VPrintf(0,
                "[CHK-I] Tag mismatch detected at address %p: ptr tag=%08x mem "
                "tag=%08x\n",
                (void*)p, PtrTagInt, ShadowTagInt);
        SigTrap<EA, AT, LogSize>(p);
      }

      break;
    case 3: /*8 bytes*/
      PtrTagLong = PtrTagByte * 0x0101010101010101ULL;
      ShadowTagLong = *(uint64_t*)shadow_addr;
      if (UNLIKELY(PtrTagLong != ShadowTagLong)) {
        VPrintf(0,
                "[CHK-L] Tag mismatch detected at address %p: ptr tag=%016lx "
                "mem tag=%016lx\n",
                (void*)p, PtrTagLong, ShadowTagLong);
        SigTrap<EA, AT, LogSize>(p);
      }
      break;
    case 4: /*16 bytes*/
      PtrTagLong = PtrTagByte * 0x0101010101010101ULL;
      ShadowTagLong = *(uint64_t*)shadow_addr;
      if (UNLIKELY(PtrTagLong != ShadowTagLong)) {
        VPrintf(0,
                "[CHK-16B] Tag mismatch detected at address %p: ptr tag=%016lx "
                "mem tag=%016lx\n",
                (void*)p, PtrTagLong, ShadowTagLong);
        SigTrap<EA, AT, LogSize>(p);
      }

      else {
        ShadowTagLong = *(uint64_t*)(shadow_addr + 8);
        if (UNLIKELY(PtrTagLong != ShadowTagLong)) {
          VPrintf(0,
                  "[CHK-16B] Tag mismatch detected at address %p: ptr "
                  "tag=%016lx mem tag=%016lx\n",
                  (void*)p, PtrTagLong, ShadowTagLong);
          SigTrap<EA, AT, LogSize>(p);
        }
      }
      break;
  }
  // atomic_fetch_add(&total_checks, 1ULL, memory_order_relaxed);
  // if (atomic_load(&total_checks, memory_order_relaxed) == 0) {
  //   // overflow detected
  //   atomic_fetch_add(&overflows_on_total_checks, 1ULL, memory_order_relaxed);
  // }
}

}  // end namespace __hwasan

#endif  // HWASAN_CHECKS_H
