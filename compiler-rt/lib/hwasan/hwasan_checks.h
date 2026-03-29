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

#define getT(tag) (tag & 0b00111111UL)
#define getL(tag) (tag & 0b00110000UL) >> 4
#define getR(tag) (tag & 0b01000000UL) >> 6

template <ErrorAction EA, AccessType AT>
__attribute__((always_inline, nodebug)) static void CheckAddressSized(uptr p,
                                                                      uptr sz) {
  if (sz == 0 || !InTaggableRegion(p)) {
    return;
  }

  unsigned char* untagged_ptr = (unsigned char*)(p & ~kAddressTagMask);
  tag_t ptr_tag = GetTagFromPointer(p);

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
  }

  uptr baseShadow = MemToShadow((uptr)untagged_ptr);
  uint8_t mem_tag = *(uint8_t*)baseShadow;
  bool memIsNull = mem_tag == 0UL;
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
    return;
  }

  unsigned int size = (unsigned int)sz;
  unsigned int chunks8B = size / 8;
  unsigned int remainder = size % 8;
  uint64_t ptr_tag_8B = ptr_tag * 0x0101010101010101ULL;

  uint64_t extendedMemTag;
  for (unsigned int i = 0; i < chunks8B; i++) {
    extendedMemTag = *(uint64_t*)(baseShadow + i * 8) &
                     0x3F3F3F3F3F3F3F3FUL;  // only get T bits
    if (UNLIKELY(extendedMemTag != ptr_tag_8B)) {
      VPrintf(0, "[HWASAN] Tag mismatch detected at address %p: ptr tag=%02x mem tag=%02x\n",
              (void*)(p + i * 8), ptr_tag_8B, getT(extendedMemTag));
      SigTrap<EA, AT>(p, sz);
      if (EA == ErrorAction::Abort)
        __builtin_unreachable();
    }
  }  // for

  uptr curShadow = baseShadow + chunks8B * 8;
  // uptr curShadow = baseShadow;
  for (unsigned int i = 0; i < remainder; i++) {
    // for (unsigned int i = 0; i < size; i++) {
    tag_t mem_tag = *(tag_t*)(curShadow + i);
    // NOTE: memtag can become 0 at some point if a) going out of bounds on
    // the current object b) flexible array member. We tolerate a), but have
    // to be lenient on b)
    // if (UNLIKELY(getT(mem_tag) != getT(ptr_tag))) {  //  && mem_tag != 0
    if (UNLIKELY(mem_tag != ptr_tag)) {  //  && mem_tag != 0
      VPrintf(0, "[HWASAN] Tag mismatch detected at address %p: ptr tag=%02x mem tag=%02x\n",
              (void*)(p + i), ptr_tag, mem_tag);
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
  if (!InTaggableRegion(p))
    return;
  // NOTE: levels are masked for now, but they could be removed to make this
  // check even faster

  uint8_t tag = GetTagFromPointer(p) & 0x3FUL;  // only get T bits
  uptr untagged_ptr = UntagAddr(p);             // this could be avoided
  uptr shadow_addr = MemToShadow(untagged_ptr);
  uint8_t ShadowTag = getT(*(uint8_t*)shadow_addr);
  // DEBUG
  if (UNLIKELY(ShadowTag == 0)) {
    atomic_fetch_add(&checks_on_uninited_shadow, 1ULL, memory_order_relaxed);

    if (atomic_load(&checks_on_uninited_shadow, memory_order_relaxed) == 0) {
      // overflow detected
      atomic_fetch_add(&overflows_on_uninited_shadow_checks, 1ULL,
                       memory_order_relaxed);
    }
    return;
  }
  if (UNLIKELY(GetTagFromPointer(p) == 0)) {
    atomic_fetch_add(&checks_on_untagged_ptr, 1ULL, memory_order_relaxed);
    if (atomic_load(&checks_on_untagged_ptr, memory_order_relaxed) == 0) {
      // overflow detected
      atomic_fetch_add(&overflows_on_untagged_ptr_checks, 1ULL,
                       memory_order_relaxed);
    }
    return;
  }
  uint16_t TagShort = 0;
  uint16_t ShadowTagShort = 0;
  uint16_t ShadowTagMaskShort = 0x3F3FUL;  // only get T bits
  uint32_t TagInt = 0;
  uint32_t ShadowTagInt = 0;
  uint32_t ShadowTagMaskInt = 0x3F3F3F3FUL;

  uint64_t TagLong = 0;
  uint64_t ShadowTagLong = 0;
  uint64_t ShadowTagMaskLong = 0x3F3F3F3F3F3F3F3FUL;

  switch (LogSize) {
    case 0: /*byte*/
      if (UNLIKELY(tag && ShadowTag && tag != ShadowTag))
        SigTrap<EA, AT, LogSize>(p);
      break;
    case 1: /*2 bytes*/
      TagShort = (tag << 8) ^ tag;
      ShadowTagShort = *(uint16_t*)shadow_addr & ShadowTagMaskShort;
      if (UNLIKELY(TagShort && ShadowTagShort && (TagShort != ShadowTagShort)))
        SigTrap<EA, AT, LogSize>(p);
      break;
    case 2: /*4 bytes*/
      TagInt = (tag << 24) ^ (tag << 16) ^ (tag << 8) ^ tag;
      ShadowTagInt = *(uint32_t*)shadow_addr & ShadowTagMaskInt;
      if (UNLIKELY(TagInt && ShadowTagInt && (TagInt != ShadowTagInt)))
        SigTrap<EA, AT, LogSize>(p);
      break;
    case 3: /*8 bytes*/
      TagLong = ((uint64_t)tag << 56) ^ ((uint64_t)tag << 48) ^
                ((uint64_t)tag << 40) ^ ((uint64_t)tag << 32) ^
                ((uint64_t)tag << 24) ^ ((uint64_t)tag << 16) ^
                ((uint64_t)tag << 8) ^ (uint64_t)tag;
      ShadowTagLong = *(uint64_t*)shadow_addr & ShadowTagMaskLong;
      if (UNLIKELY(TagLong && ShadowTagLong && (TagLong != ShadowTagLong)))
        SigTrap<EA, AT, LogSize>(p);
      break;
    case 4: /*16 bytes*/
      TagLong = ((uint64_t)tag << 56) ^ ((uint64_t)tag << 48) ^
                ((uint64_t)tag << 40) ^ ((uint64_t)tag << 32) ^
                ((uint64_t)tag << 24) ^ ((uint64_t)tag << 16) ^
                ((uint64_t)tag << 8) ^ (uint64_t)tag;
      ShadowTagLong = *(uint64_t*)shadow_addr & ShadowTagMaskLong;
      if (UNLIKELY(TagLong && ShadowTagLong && (TagLong != ShadowTagLong)))
        SigTrap<EA, AT, LogSize>(p);
      else {
        ShadowTagLong = *(uint64_t*)(shadow_addr + 8) & ShadowTagMaskLong;
        if (UNLIKELY(TagLong && ShadowTagLong && (TagLong != ShadowTagLong)))
          SigTrap<EA, AT, LogSize>(p);
      }
      break;
  }
  atomic_fetch_add(&total_checks, 1ULL, memory_order_relaxed);
  if (atomic_load(&total_checks, memory_order_relaxed) == 0) {
    // overflow detected
    atomic_fetch_add(&overflows_on_total_checks, 1ULL, memory_order_relaxed);
  }
}

}  // end namespace __hwasan

#endif  // HWASAN_CHECKS_H
