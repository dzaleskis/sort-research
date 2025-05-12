#include "thirdparty/timsort-cpp-og/include/tim/timsort.h"

#include <compare>
#include <stdexcept>
#include <vector>

#include <stdint.h>

#include "shared.h"

// // timsort is implemented in a way that requires that T implements a default
// // constructor. That's incompatible with move only types such as FFIStringCpp.
// #define SORT_INCOMPATIBLE_WITH_SEMANTIC_CPP_TYPE

template <typename T, typename F>
uint32_t sort_by_impl(T* data, size_t len, F cmp_fn, uint8_t* ctx) noexcept {
  try {
      // Powersort does not provide a way to specify a custom comparator function,
      // so we have to wrap it inside a type with custom comparison function.
      CompWrapper<T, F>::cmp_fn_local = cmp_fn;
      CompWrapper<T, F>::ctx_local = ctx;

      // Let's just pray they are layout equivalent.
      tim::timsort(
          reinterpret_cast<CompWrapper<T, F>*>(data),
          reinterpret_cast<CompWrapper<T, F>*>(data + len));
  } catch (...) {
    return 1;
  }

  return 0;
}

extern "C" {
// --- i32 ---

void timsort_stable_og_i32(int32_t* data, size_t len) {
  tim::timsort(data, data + len);
}

uint32_t timsort_stable_og_i32_by(int32_t* data,
                                 size_t len,
                                 CompResult (*cmp_fn)(const int32_t&,
                                                      const int32_t&,
                                                      uint8_t*),
                                 uint8_t* ctx) {
  return sort_by_impl(data, len, cmp_fn, ctx);
}

// --- u64 ---

void timsort_stable_og_u64(uint64_t* data, size_t len) {
  tim::timsort(data, data + len);
}

uint32_t timsort_stable_og_u64_by(uint64_t* data,
                                 size_t len,
                                 CompResult (*cmp_fn)(const uint64_t&,
                                                      const uint64_t&,
                                                      uint8_t*),
                                 uint8_t* ctx) {
  return sort_by_impl(data, len, cmp_fn, ctx);
}

// --- ffi_string ---

void timsort_stable_og_ffi_string(FFIString* data, size_t len) {
  tim::timsort(reinterpret_cast<FFIStringCpp*>(data),
          reinterpret_cast<FFIStringCpp*>(data) + len);
}

uint32_t timsort_stable_og_ffi_string_by(FFIString* data,
                                        size_t len,
                                        CompResult (*cmp_fn)(const FFIString&,
                                                             const FFIString&,
                                                             uint8_t*),
                                        uint8_t* ctx) {
  return sort_by_impl(reinterpret_cast<FFIStringCpp*>(data), len, cmp_fn, ctx);
}

// --- f128 ---

void timsort_stable_og_f128(F128* data, size_t len) {
  tim::timsort(reinterpret_cast<F128Cpp*>(data),
          reinterpret_cast<F128Cpp*>(data) + len);
}

uint32_t timsort_stable_og_f128_by(F128* data,
                                  size_t len,
                                  CompResult (*cmp_fn)(const F128&,
                                                       const F128&,
                                                       uint8_t*),
                                  uint8_t* ctx) {
  return sort_by_impl(reinterpret_cast<F128Cpp*>(data), len, cmp_fn, ctx);
}

// --- 1k ---

void timsort_stable_og_1k(FFIOneKibiBit* data, size_t len) {
  tim::timsort(reinterpret_cast<FFIOneKiloByteCpp*>(data),
          reinterpret_cast<FFIOneKiloByteCpp*>(data) + len);
}

uint32_t timsort_stable_og_1k_by(FFIOneKibiBit* data,
                                size_t len,
                                CompResult (*cmp_fn)(const FFIOneKibiBit&,
                                                     const FFIOneKibiBit&,
                                                     uint8_t*),
                                uint8_t* ctx) {
  return sort_by_impl(reinterpret_cast<FFIOneKiloByteCpp*>(data), len, cmp_fn,
                      ctx);
}
}  // extern "C"
