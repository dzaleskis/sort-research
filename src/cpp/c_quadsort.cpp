#include "thirdparty/scandum/quadsort.h"

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
    quadsort(static_cast<void*>(data), len, sizeof(T),
             make_compare_fn_c(cmp_fn, ctx));
  } catch (...) {
    return 1;
  }

  return 0;
}

extern "C" {
// --- i32 ---

void quadsort_stable_i32(int32_t* data, size_t len) {
  quadsort_prim(static_cast<void*>(data), len, /*signed int*/ 4);
}

uint32_t quadsort_stable_i32_by(int32_t* data,
                                size_t len,
                                CompResult (*cmp_fn)(const int32_t&,
                                                     const int32_t&,
                                                     uint8_t*),
                                uint8_t* ctx) {
  return sort_by_impl(data, len, cmp_fn, ctx);
}

// --- u64 ---

void quadsort_stable_u64(uint64_t* data, size_t len) {
  quadsort_prim(static_cast<void*>(data), len, /*unsigned long long*/ 9);
}

uint32_t quadsort_stable_u64_by(uint64_t* data,
                                size_t len,
                                CompResult (*cmp_fn)(const uint64_t&,
                                                     const uint64_t&,
                                                     uint8_t*),
                                uint8_t* ctx) {
  return sort_by_impl(data, len, cmp_fn, ctx);
}

// --- ffi_string ---

void quadsort_stable_ffi_string(FFIString* data, size_t len) {
    FFIString** ptrArray = static_cast<FFIString**>(malloc(sizeof(FFIString*) * len));
    for (int i = 0; i < len; i++) {
        ptrArray[i] = &data[i];
    }

    quadsort(static_cast<void*>(ptrArray), len, sizeof(FFIString*), indirect_c_cmp_func<FFIStringCpp>);

    FFIString* outArray = static_cast<FFIString*>(malloc(sizeof(FFIString) * len));
    for (int i = 0; i < len; i++) {
        outArray[i] = *ptrArray[i];
    }

    for (int i = 0; i < len; i++) {
        data[i] = outArray[i];
    }
}

uint32_t quadsort_stable_ffi_string_by(FFIString* data,
                                       size_t len,
                                       CompResult (*cmp_fn)(const FFIString&,
                                                            const FFIString&,
                                                            uint8_t*),
                                       uint8_t* ctx) {
  printf("Not supported\n");
  return 1;
}

// --- f128 ---

void quadsort_stable_f128(F128* data, size_t len) {
  F128** ptrArray = static_cast<F128**>(malloc(sizeof(F128*) * len));
  for (int i = 0; i < len; i++) {
      ptrArray[i] = &data[i];
  }

  quadsort(static_cast<void*>(ptrArray), len, sizeof(F128*), indirect_c_cmp_func<F128Cpp>);

  F128* outArray = static_cast<F128*>(malloc(sizeof(F128) * len));
  for (int i = 0; i < len; i++) {
      outArray[i] = *ptrArray[i];
  }

  for (int i = 0; i < len; i++) {
      data[i] = outArray[i];
  }
}

uint32_t quadsort_stable_f128_by(F128* data,
                                 size_t len,
                                 CompResult (*cmp_fn)(const F128&,
                                                      const F128&,
                                                      uint8_t*),
                                 uint8_t* ctx) {
  printf("Not supported\n");
  return 1;
}

// --- 1k ---

void quadsort_stable_1k(FFIOneKibiBit* data, size_t len) {
    FFIOneKibiBit** ptrArray = static_cast<FFIOneKibiBit**>(malloc(sizeof(FFIOneKibiBit*) * len));
    for (int i = 0; i < len; i++) {
        ptrArray[i] = &data[i];
    }

    quadsort(static_cast<void*>(ptrArray), len, sizeof(FFIOneKibiBit*), indirect_c_cmp_func<FFIOneKiloByteCpp>);

    FFIOneKibiBit* outArray = static_cast<FFIOneKibiBit*>(malloc(sizeof(FFIOneKibiBit) * len));
    for (int i = 0; i < len; i++) {
        outArray[i] = *ptrArray[i];
    }

    for (int i = 0; i < len; i++) {
        data[i] = outArray[i];
    }
}

uint32_t quadsort_stable_1k_by(FFIOneKibiBit* data,
                               size_t len,
                               CompResult (*cmp_fn)(const FFIOneKibiBit&,
                                                    const FFIOneKibiBit&,
                                                    uint8_t*),
                               uint8_t* ctx) {
  printf("Not supported\n");
  return 1;
}
}  // extern "C"
