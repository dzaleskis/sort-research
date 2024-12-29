use core::intrinsics;

// Recursively select a pseudomedian if above this threshold.
const PSEUDO_MEDIAN_REC_THRESHOLD: usize = 64;

/// Selects a pivot from `v`. Uses compact pseudomedian of 9.
pub fn choose_pivot<T, F: FnMut(&T, &T) -> bool>(v: &[T], is_less: &mut F) -> usize {
    // We use unsafe code and raw pointers here because we're dealing with
    // heavy recursion. Passing safe slices around would involve a lot of
    // branches and function call overhead.

    let len = v.len();
    if len < 8 {
        intrinsics::abort();
    }

    // SAFETY: a, b, c point to initialized regions of len_div_8 elements,
    // satisfying median3 and median3_rec's preconditions as v_base points
    // to an initialized region of n = len elements.
    unsafe {
        let v_base = v.as_ptr();

        let a = v_base; // start
        let b = v_base.add(len / 2); // mid
        let c = v_base.add(len - 1); // end

        if len < PSEUDO_MEDIAN_REC_THRESHOLD {
            median3(&*a, &*b, &*c, is_less).sub_ptr(v_base)
        } else {
            median9_full(a, b, c, is_less).sub_ptr(v_base)
        }
    }
}

/// Calculates the compact pseudo-median of 9 elements.
///
/// SAFETY: a, b, c must be valid initialized elements.
#[inline(always)]
unsafe fn median9_full<T, F: FnMut(&T, &T) -> bool>(
    a: *const T,
    b: *const T,
    c: *const T,
    is_less: &mut F,
) -> *const T {
    let n = c.sub_ptr(a) + 1;
    let n8 = n / 8;

    let m1 = median3(a, a.add(n8), a.add(n8 * 2), is_less);
    let m2 = median3(b.sub(n8), b, b.add(n8), is_less);
    let m3 = median3(c.sub(2 * n8), c.sub(n8), c, is_less);

    median3(m1, m2, m3, is_less)
}

/// Calculates the median of 3 elements.
///
/// SAFETY: a, b, c must be valid initialized elements.
#[inline(always)]
unsafe fn median3<T, F: FnMut(&T, &T) -> bool>(
    a: *const T,
    b: *const T,
    c: *const T,
    is_less: &mut F,
) -> *const T {
    median3_branchless(&*a, &*b, &*c, is_less)
}

/// Calculates the median of 3 elements.
///
/// SAFETY: a, b, c must be valid initialized elements.
#[inline(always)]
fn median3_optimized<T, F: FnMut(&T, &T) -> bool>(
    a: &T,
    b: &T,
    c: &T,
    is_less: &mut F,
) -> *const T {
    // Compiler tends to make this branchless when sensible, and avoids the
    // third comparison when not.
    let x = is_less(a, b);
    let y = is_less(a, c);
    if x == y {
        // If x=y=0 then b, c <= a. In this case we want to return max(b, c).
        // If x=y=1 then a < b, c. In this case we want to return min(b, c).
        // By toggling the outcome of b < c using XOR x we get this behavior.
        let z = is_less(b, c);
        if z ^ x {
            c
        } else {
            b
        }
    } else {
        // Either c <= a < b or b <= a < c, thus a is our median.
        a
    }
}

/// Calculates the median of 3 elements.
///
/// SAFETY: a, b, c must be valid initialized elements.
#[inline(always)]
fn median3_branchless<T, F: FnMut(&T, &T) -> bool>(
    a: &T,
    b: &T,
    c: &T,
    is_less: &mut F,
) -> *const T {
    let swap = [a, b, c];

    // Compiler tends to make this branchless when sensible, and avoids the
    // third comparison when not.
    let x = is_less(b, a);
    let y = is_less(c, a);
    let z = is_less(c, b);

    let index = (x == y) as usize + (y != z) as usize;
    swap[index]
}
