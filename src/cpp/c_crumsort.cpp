#include "thirdparty/scandum/crumsort.h"

#include <cstdlib>
#include <stdexcept>

#include <stdint.h>

#include "shared.h"

template <typename T>
uint32_t sort_by_impl(T* data,
                      size_t len,
                      CompResult (*cmp_fn)(const T&, const T&, uint8_t*),
                      uint8_t* ctx) noexcept {
  try {
    crumsort(static_cast<void*>(data), len, sizeof(T),
             make_compare_by_fn_c(cmp_fn, ctx));
  } catch (...) {
    return 1;
  }

  return 0;
}

template <typename T, typename T_CPP>
uint32_t indirect_sort_impl(T* data,size_t len) noexcept {
  try {
      T** ptrArray = static_cast<T**>(malloc(sizeof(T*) * len));
      for (int i = 0; i < len; i++) {
          ptrArray[i] = &data[i];
      }

      crumsort(static_cast<void*>(ptrArray), len, sizeof(T*), indirect_c_cmp_func<T_CPP>);

      T* outArray = static_cast<T*>(malloc(sizeof(T) * len));
      for (int i = 0; i < len; i++) {
          outArray[i] = *ptrArray[i];
      }

      for (int i = 0; i < len; i++) {
          data[i] = outArray[i];
      }
  } catch (...) {
    return 1;
  }

  return 0;
}

template <typename T>
uint32_t indirect_sort_by_impl(T* data,size_t len, CompResult (*cmp_fn)(const T&, const T&, uint8_t*), uint8_t* ctx) noexcept {
  try {
      T** ptrArray = static_cast<T**>(malloc(sizeof(T*) * len));
      for (int i = 0; i < len; i++) {
          ptrArray[i] = &data[i];
      }

      crumsort(static_cast<void*>(ptrArray), len, sizeof(T*), make_indirect_compare_by_fn_c(cmp_fn, ctx));

      T* outArray = static_cast<T*>(malloc(sizeof(T) * len));
      for (int i = 0; i < len; i++) {
          outArray[i] = *ptrArray[i];
      }

      for (int i = 0; i < len; i++) {
          data[i] = outArray[i];
      }
  } catch (...) {
    return 1;
  }

  return 0;
}

extern "C" {
// --- i32 ---

void crumsort_unstable_i32(int32_t* data, size_t len) {
  crumsort_prim(static_cast<void*>(data), len, /*signed int*/ 4);
}

uint32_t crumsort_unstable_i32_by(int32_t* data,
                                size_t len,
                                CompResult (*cmp_fn)(const int32_t&,
                                                     const int32_t&,
                                                     uint8_t*),
                                uint8_t* ctx) {
  return sort_by_impl(data, len, cmp_fn, ctx);
}

// --- u64 ---

void crumsort_unstable_u64(uint64_t* data, size_t len) {
  crumsort_prim(static_cast<void*>(data), len, /*unsigned long long*/ 9);
}

uint32_t crumsort_unstable_u64_by(uint64_t* data,
                                size_t len,
                                CompResult (*cmp_fn)(const uint64_t&,
                                                     const uint64_t&,
                                                     uint8_t*),
                                uint8_t* ctx) {
  return sort_by_impl(data, len, cmp_fn, ctx);
}

// --- ffi_string ---

void crumsort_unstable_ffi_string(FFIString* data, size_t len) {
    indirect_sort_impl<FFIString, FFIStringCpp>(data, len);
}

uint32_t crumsort_unstable_ffi_string_by(FFIString* data,
                                       size_t len,
                                       CompResult (*cmp_fn)(const FFIString&,
                                                            const FFIString&,
                                                            uint8_t*),
                                       uint8_t* ctx) {
    return indirect_sort_by_impl<FFIString>(data, len, cmp_fn, ctx);
}

// --- f128 ---

void crumsort_unstable_f128(F128* data, size_t len) {
  indirect_sort_impl<F128, F128Cpp>(data, len);
}

uint32_t crumsort_unstable_f128_by(F128* data,
                                 size_t len,
                                 CompResult (*cmp_fn)(const F128&,
                                                      const F128&,
                                                      uint8_t*),
                                 uint8_t* ctx) {
    return indirect_sort_by_impl<F128>(data, len, cmp_fn, ctx);
}

// --- 1k ---

void crumsort_unstable_1k(FFIOneKibiBit* data, size_t len) {
    indirect_sort_impl<FFIOneKibiBit, FFIOneKiloByteCpp>(data, len);
}

uint32_t crumsort_unstable_1k_by(FFIOneKibiBit* data,
                               size_t len,
                               CompResult (*cmp_fn)(const FFIOneKibiBit&,
                                                    const FFIOneKibiBit&,
                                                    uint8_t*),
                               uint8_t* ctx) {
    return indirect_sort_by_impl<FFIOneKibiBit>(data, len, cmp_fn, ctx);
}
}  // extern "C"
