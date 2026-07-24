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

#if defined(__aarch64__)
#  define T_BITS 5UL
#  define L_BITS 2UL
#  define L_MASK (0b11U << T_BITS)
#else
#  define T_BITS 3UL
#  define L_BITS 2UL
#  define L_MASK (0b11UL << T_BITS)
#endif
#define R_MASK (1UL << (T_BITS + L_BITS))
#define getT(tag) (tag & ((1UL << T_BITS) - 1))
#define getL(tag) ((tag & L_MASK) >> T_BITS)
#define getR(tag) ((tag & R_MASK) >> (T_BITS + L_BITS))

// This mask preserves the bits on which we do checks
// #define CHECK_TAG_MASK ((1ULL << (T_BITS + L_BITS)) - 1)
#define CHECK_TAG_MASK ((1ULL << (T_BITS + L_BITS)) - 1)

// TODO: double check on overflows on tagging bytes -> shadow byte == 0xff means
// padding
#define PADDING_BYTE 0xff
// TODO: how to detect a byte exactly equal to 0xff inside a 64 bit value
// efficiently?
// HEURISTIC: only checking on the last byte for now

template <ErrorAction EA, AccessType AT>
__attribute__((always_inline, nodebug)) static void CheckAddressSized(uptr p,
                                                                      uptr sz) {
  unsigned char* untagged_ptr = (unsigned char*)(p & ~kAddressTagMask);
  tag_t ptr_tag = GetTagFromPointer(p);
  // when ptr tag is 0, we skip checks

  if (UNLIKELY(ptr_tag == 0)) {
    VPrintf(2, "[CheckAddressSized] ptr tag is 0, ptr=%p sz=%lu\n", (void*)p, sz);
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
  // bool memIsNull = (mem_tag & CHECK_TAG_MASK) == 0;
  bool memIsNull = (mem_tag) == 0; // TODO: change back
  // NOTE: do check on first byte, catch the smallest read possible

  if (UNLIKELY(memIsNull)) {
    VPrintf(2, "[CheckAddressSized] memtag is 0, ptr=%p sz=%lu\n", (void*)p, sz);
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
      if(UNLIKELY(ShadowTagByte != 0)) {
        VPrintf(
            0,
            "[check-null] Tag mismatch detected at address %p: ptr "
            "tag=%02x mem tag=%02x \n\t PL=%02x ML=%02x \n\t PT=%02x MT=%02x\n",
            (void*)p, ptr_tag, ShadowTagByte, getL(ptr_tag), getL(ShadowTagByte),
            getT(ptr_tag), getT(ShadowTagByte));
        SigTrap<EA, AT>(p, sz);
      }
    }
    return;
  }  // memtag is 0

  bool RSet = getR(ptr_tag);
  if (RSet) {
    // TODO
    VPrintf(2, "[CheckAddressSized] R CHK: L=%02x, T=%02x, R=%02x, P = %p\n",
            getL(ptr_tag), getT(ptr_tag), getR(ptr_tag), (void*)p);
    return;
  }  // RSet

  VPrintf(2, "[CheckAddressSized] ptr=%p sz=%lu\n", (void*)p, sz);
  unsigned int size = (unsigned int)sz;
  if (size == 0)
    return;  // no access, so no check needed

  unsigned int chunks8B = size / 8;
  unsigned int remainder = size % 8;

  uint8_t ptr_L = getL(ptr_tag);
  uint8_t mem_L = getL(mem_tag);

  VPrintf(2, "[CheckAddressSized] L bits: ptr_L=%02x mem_L=%02x\n", ptr_L,
          mem_L);

  uint64_t extension_mask = 0x0101010101010101ULL;

  uint64_t ptr_T_8B = ptr_tag * (extension_mask);
  uint64_t extendedMask = CHECK_TAG_MASK * extension_mask;
  ptr_T_8B = ptr_T_8B & extendedMask;  // only get bits you want

  uint64_t mem_T_8B = -1LL;

  for (unsigned int i = 0; i < chunks8B; i++) {
    mem_T_8B = (*(uint64_t*)(baseShadow + i * 8)) &
               (CHECK_TAG_MASK * extension_mask);  // only get bits you want

    // TODO: detect padding since, in case of 8B access where tag is 0x7 on ptr
    // and 0xff on memory, we have a FN
    // NOTE: masking & checking for padding bytes are tricky to implement
    // together. If masking out the bits telling that is a padding byte, you
    // could have FPs when the tag has the T LSBs set

    if (UNLIKELY((mem_T_8B != ptr_T_8B) ||
                 (((*(uint8_t*)(baseShadow + i * 8 + 7))) == PADDING_BYTE))) {
      // TODO: this can be made better
      VPrintf(
          0,
          "[CheckAddressSized-pre] Tag mismatch detected at address %p: ptr "
          "tag=%016lx mem tag=%016lx\n",
          (void*)(p + i * 8), ptr_T_8B, mem_T_8B);
      SigTrap<EA, AT>(p, sz);
      if (EA == ErrorAction::Abort)
        __builtin_unreachable();
    }
  }  // for

  // BYTE-granular tail checks
  uint64_t ptr_T_B = ptr_tag & CHECK_TAG_MASK;  // only get bits you want
  uptr curShadow = baseShadow + chunks8B * 8;
  for (unsigned int i = 0; i < remainder; i++) {
    tag_t mem_T_B = (*(tag_t*)(curShadow + i)) & CHECK_TAG_MASK;
    // NOTE: memtag can become 0 at some point if a) going out of bounds on
    // the current object b) flexible array member. We tolerate a), but have
    // to be lenient on b)
    if (UNLIKELY((mem_T_B != ptr_T_B) || mem_T_B == PADDING_BYTE)) {
      VPrintf(0,
              "[CheckAddressSized-tail] Tag mismatch detected at address %p: "
              "ptr tag=%02lx "
              "mem tag=%02lx, ptrL=%02x, memL=%02x\n",
              (void*)(p + i), ptr_T_B, mem_T_B, ptr_L, mem_L);
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
  // NOTE: levels are masked for now, but they could be removed to make this
  // check even faster

  uint8_t tag = GetTagFromPointer(p);
  uptr untagged_ptr = UntagAddr(p);
  uptr shadow_addr = MemToShadow(untagged_ptr);
  // uint8_t ShadowTag = (*(uint8_t*)shadow_addr) & CHECK_TAG_MASK;  // TODO: analyze FN cases
  uint8_t ShadowTag =
      (*(uint8_t*)shadow_addr);  // TODO: change backk

  // DEBUG
  if (UNLIKELY(GetTagFromPointer(p) == 0)) {
    VPrintf(2, "[CheckAddress] untagged ptr detected at address %p\n", (void*)p);
    // atomic_fetch_add(&checks_on_untagged_ptr, 1ULL, memory_order_relaxed);
    // if (atomic_load(&checks_on_untagged_ptr, memory_order_relaxed) == 0) {
    //   // overflow detected
    //   atomic_fetch_add(&overflows_on_untagged_ptr_checks, 1ULL,
    //                    memory_order_relaxed);
    // }
    return;
  }
  
  if (UNLIKELY(ShadowTag == 0)) {
    VPrintf(2, "[CheckAddress] uninited shadow detected at address %p\n", (void*)p);
    // atomic_fetch_add(&checks_on_uninited_shadow, 1ULL, memory_order_relaxed);

    // if (atomic_load(&checks_on_uninited_shadow, memory_order_relaxed) == 0) {
    //   // overflow detected
    //   atomic_fetch_add(&overflows_on_uninited_shadow_checks, 1ULL,
    //                    memory_order_relaxed);
    // }
    // check that ALL the bytes in the access are zero. If not, raise error.
    for (unsigned int i = 0; i < (1 << LogSize); i++) {
      uint8_t ShadowTagByte = *(uint8_t*)(shadow_addr + i);
      if(UNLIKELY(ShadowTagByte != 0)) {
        VPrintf(
            0,
            "[check-null] Tag mismatch detected at address %p: ptr "
            "tag=%02x mem tag=%02x \n\t PL=%02x ML=%02x \n\t PT=%02x MT=%02x\n",
            (void*)p, tag, ShadowTagByte, getL(tag), getL(ShadowTagByte),
            getT(tag), getT(ShadowTagByte));
        SigTrap<EA, AT, LogSize>(p);
      }
    }
    return;
  }
  VPrintf(2, "[CheckAddress] ptr=%p sz=%d\n", (void*)p, 1 << LogSize);

  // bool isRP = getR(tag);
  // if (isRP) {
    // TODO: use this to debug loops at O2
    // TODO: do we want to keep this kind of check? Or do we delegate this check
    // to type sanitizers? It's FP-prone on C++
    // VPrintf(2, "[CheckAddress] R PTR %p, SZ %d\n", (void*)p, 1 << LogSize);
  //   return;
  // }
  // VPrintf(2, "[CheckAddress] NON-RP PTR %p, SZ %d\n", (void*)p, 1 << LogSize);

  auto ptr_L = getL(tag);
  auto mem_L = getL(ShadowTag);

  uint8_t ShadowTagByte = 0;
  uint8_t TagByte = tag;
  uint8_t MaskTagByte = (uint8_t)CHECK_TAG_MASK;

  uint16_t TagShort = 0;
  uint16_t ShadowTagShort = 0;
  uint16_t MaskTagShort = (uint16_t)CHECK_TAG_MASK * 0x0101U;

  uint32_t TagInt = 0;
  uint32_t ShadowTagInt = 0;
  uint32_t MaskTagInt = (uint32_t)CHECK_TAG_MASK * 0x01010101U;

  uint64_t TagLong = 0;
  uint64_t ShadowTagLong = 0;
  uint64_t MaskTagLong = (uint64_t)CHECK_TAG_MASK * 0x0101010101010101ULL;

  switch (LogSize) {
    case 0: /*byte*/
      ShadowTagByte = *(uint8_t*)shadow_addr & MaskTagByte;
      TagByte = TagByte & MaskTagByte;
      if (UNLIKELY(/*TagByte && ShadowTagByte && */ TagByte != ShadowTagByte ||
                   (/*TagByte && ShadowTagByte &&*/
                    (*(uint8_t*)shadow_addr == PADDING_BYTE)))) {
        VPrintf(
            0,
            "[check-byte] Tag mismatch detected at address %p: ptr "
            "tag=%02x mem tag=%02x \n\t PL=%02x ML=%02x \n\t PT=%02x MT=%02x\n",
            (void*)p, TagByte, ShadowTagByte, ptr_L, mem_L, getT(tag),
            getT(ShadowTag));
        SigTrap<EA, AT, LogSize>(p);
      }
      break;
    case 1: /*2 bytes*/
      TagShort = (TagByte << 8) ^ TagByte;
      TagShort = TagShort & MaskTagShort;
      ShadowTagShort = *(uint16_t*)shadow_addr;
      ShadowTagShort = ShadowTagShort & MaskTagShort;
      if (UNLIKELY(/*TagShort && ShadowTagShort && */(TagShort != ShadowTagShort) ||
                   (/*TagShort && ShadowTagShort &&*/
                    (((*(uint16_t*)shadow_addr >> 8)) == PADDING_BYTE)))) {
        VPrintf(0,
                "[check-short] Tag mismatch detected at address %p: ptr "
                "tag=%04x mem tag=%04x, PL=%02x ML=%02x\n\t PT=%02x MT=%02x\n",
                (void*)p, TagShort, ShadowTagShort, ptr_L, mem_L, getT(tag),
                getT(ShadowTag));
        SigTrap<EA, AT, LogSize>(p);
      }
      break;

    case 2: /*4 bytes*/
      TagInt = (TagByte << 24) ^ (TagByte << 16) ^ (TagByte << 8) ^ TagByte;
      TagInt = TagInt & MaskTagInt;
      ShadowTagInt = *(uint32_t*)shadow_addr;
      ShadowTagInt = ShadowTagInt & MaskTagInt;
      if (UNLIKELY(/*TagInt && ShadowTagInt && */(TagInt != ShadowTagInt) ||
                   (/*TagInt && ShadowTagInt &&*/
                    (((*(uint32_t*)shadow_addr >> 24)) == PADDING_BYTE)))) {
        VPrintf(0,
                "[check-int] Tag mismatch detected at address %p: ptr "
                "tag=%04lx mem tag=%04lx\n\t PL=%02x ML=%02x \n\t PT=%02x "
                "MT=%02x\n",
                (void*)p, TagInt, ShadowTagInt, ptr_L, mem_L, getT(tag),
                getT(ShadowTag));
        SigTrap<EA, AT, LogSize>(p);
      }

      break;
    case 3: /*8 bytes*/
      TagLong = ((uint64_t)TagByte << 56) ^ ((uint64_t)TagByte << 48) ^
                ((uint64_t)TagByte << 40) ^ ((uint64_t)TagByte << 32) ^
                ((uint64_t)TagByte << 24) ^ ((uint64_t)TagByte << 16) ^
                ((uint64_t)TagByte << 8) ^ (uint64_t)TagByte;
      TagLong = TagLong & MaskTagLong;
      ShadowTagLong = *(uint64_t*)shadow_addr;
      ShadowTagLong = ShadowTagLong & MaskTagLong;
      if (UNLIKELY(/*TagLong && ShadowTagLong && */(TagLong != ShadowTagLong) ||
                   (/*TagLong && ShadowTagLong &&*/
                    (((*(uint64_t*)shadow_addr >> 56)) == PADDING_BYTE)))) {
        VPrintf(0,
                "[check-long] Tag mismatch detected at address %p: ptr "
                "tag=%016lx mem tag=%016lx, \n\t PL=%02x ML=%02x\n\t PT=%02x "
                "MT=%02x\n",
                (void*)p, TagLong, ShadowTagLong, ptr_L, mem_L, getT(tag),
                getT(ShadowTag));
        SigTrap<EA, AT, LogSize>(p);
      }
      break;
    case 4: /*16 bytes*/
      TagLong = ((uint64_t)TagByte << 56) ^ ((uint64_t)TagByte << 48) ^
                ((uint64_t)TagByte << 40) ^ ((uint64_t)TagByte << 32) ^
                ((uint64_t)TagByte << 24) ^ ((uint64_t)TagByte << 16) ^
                ((uint64_t)TagByte << 8) ^ (uint64_t)TagByte;
      ShadowTagLong = *(uint64_t*)shadow_addr;
      TagLong = TagLong & MaskTagLong;
      ShadowTagLong = ShadowTagLong & MaskTagLong;
      if (UNLIKELY(/*TagLong && ShadowTagLong && */(TagLong != ShadowTagLong) ||
                   (/*TagLong && ShadowTagLong &&*/
                    (((*(uint64_t*)shadow_addr >> 56)) == PADDING_BYTE)))) {
        VPrintf(0,
                "[check-16B] Tag mismatch detected at address %p: ptr "
                "tag=%016lx mem tag=%016lx \n\t PL=%02x ML=%02x \n\t PT=%02x "
                "MT=%02x\n",
                (void*)(p), TagLong, ShadowTagLong, ptr_L, mem_L, getT(tag),
                getT(ShadowTag));
        SigTrap<EA, AT, LogSize>(p);
      }

      else {
        ShadowTagLong = *(uint64_t*)(shadow_addr + 8);
        ShadowTagLong = ShadowTagLong & MaskTagLong;
        if (UNLIKELY(
                /*TagLong && ShadowTagLong &&*/ (TagLong != ShadowTagLong) ||
                (/*TagLong && ShadowTagLong &&*/
                 (((*(uint64_t*)(shadow_addr + 8) >> 56)) == PADDING_BYTE)))) {
          VPrintf(0,
                  "[check-16B] Tag mismatch detected at address %p: ptr "
                  "tag=%016lx mem tag=%016lx, PL=%02x ML=%02x\n\t PT=%02x "
                  "MT=%02x\n",
                  (void*)(p + 8), TagLong, ShadowTagLong, ptr_L, mem_L,
                  getT(tag), getT(ShadowTag));
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
