#include "thirdparty/timsort-cpp-cross/include/tim/timsort.h"

#include <compare>
#include <stdexcept>
#include <vector>

#include <stdint.h>

#include "shared.h"

template <typename T, typename F>
uint32_t sort_by_impl(T* data, size_t len, F cmp_fn, uint8_t* ctx) noexcept {
  try {
    tim_cross::timsort(data, data + len, make_compare_fn<T>(cmp_fn, ctx));
  } catch (...) {
    return 1;
  }

  return 0;
}

extern "C" {
// --- i32 ---

void timsort_stable_cross_i32(int32_t* data, size_t len) {
    tim_cross::timsort(data, data + len);
}

uint32_t timsort_stable_cross_i32_by(int32_t* data,
                                 size_t len,
                                 CompResult (*cmp_fn)(const int32_t&,
                                                      const int32_t&,
                                                      uint8_t*),
                                 uint8_t* ctx) {
                                     printf("Not supported\n");
                                     return 1;
}

// --- u64 ---

void timsort_stable_cross_u64(uint64_t* data, size_t len) {
  tim_cross::timsort(data, data + len);
}

uint32_t timsort_stable_cross_u64_by(uint64_t* data,
                                 size_t len,
                                 CompResult (*cmp_fn)(const uint64_t&,
                                                      const uint64_t&,
                                                      uint8_t*),
                                 uint8_t* ctx) {
                                     printf("Not supported\n");
                                     return 1;
}

// --- ffi_string ---

void timsort_stable_cross_ffi_string(FFIString* data, size_t len) {
    printf("Not supported\n");
}

uint32_t timsort_stable_cross_ffi_string_by(FFIString* data,
                                        size_t len,
                                        CompResult (*cmp_fn)(const FFIString&,
                                                             const FFIString&,
                                                             uint8_t*),
                                        uint8_t* ctx) {
    printf("Not supported\n");
    return 1;
}

// --- f128 ---

void timsort_stable_cross_f128(F128* data, size_t len) {
    printf("Not supported\n");
}

uint32_t timsort_stable_cross_f128_by(F128* data,
                                  size_t len,
                                  CompResult (*cmp_fn)(const F128&,
                                                       const F128&,
                                                       uint8_t*),
                                  uint8_t* ctx) {
                                      printf("Not supported\n");
                                      return 1;
}

// --- 1k ---

void timsort_stable_cross_1k(FFIOneKibiBit* data, size_t len) {
    printf("Not supported\n");
}

uint32_t timsort_stable_cross_1k_by(FFIOneKibiBit* data,
                                size_t len,
                                CompResult (*cmp_fn)(const FFIOneKibiBit&,
                                                     const FFIOneKibiBit&,
                                                     uint8_t*),
                                uint8_t* ctx) {
    printf("Not supported\n");
    return 1;
}
}  // extern "C"
