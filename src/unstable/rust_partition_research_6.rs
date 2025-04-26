//! Instruction-Parallel-Network Unstable Sort, ipnsort by Lukas Bergdoll
use core::cmp;
use core::cmp::Ordering;
use core::intrinsics;
use core::mem::{self, ManuallyDrop, MaybeUninit, SizedTypeProperties};
use core::ptr;
use core::slice;

sort_impl!("partition_stable");

/// Sorts the slice, but might not preserve the order of equal elements.
///
/// This sort is unstable (i.e., may reorder equal elements), in-place
/// (i.e., does not allocate), and *O*(*n* \* log(*n*)) worst-case.
///
/// # Current implementation
///
/// The current algorithm is based on [pattern-defeating quicksort][pdqsort] by Orson Peters,
/// which combines the fast average case of randomized quicksort with the fast worst case of
/// heapsort, while achieving linear time on slices with certain patterns. It uses some
/// randomization to avoid degenerate cases, but with a fixed seed to always provide
/// deterministic behavior.
///
/// It is typically faster than stable sorting, except in a few special cases, e.g., when the
/// slice consists of several concatenated sorted sequences.
///
/// # Examples
///
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
///
/// v.sort_unstable();
/// assert!(v == [-5, -3, 1, 2, 4]);
/// ```
///
/// [pdqsort]: https://github.com/orlp/pdqsort
#[inline(always)]
pub fn sort<T>(arr: &mut [T])
where
    T: Ord,
{
    unstable_sort(arr, |a, b| a.lt(b));
}

/// Sorts the slice with a comparator function, but might not preserve the order of equal
/// elements.
///
/// This sort is unstable (i.e., may reorder equal elements), in-place
/// (i.e., does not allocate), and *O*(*n* \* log(*n*)) worst-case.
///
/// The comparator function must define a total ordering for the elements in the slice. If
/// the ordering is not total, the order of the elements is unspecified. An order is a
/// total order if it is (for all `a`, `b` and `c`):
///
/// * total and antisymmetric: exactly one of `a < b`, `a == b` or `a > b` is true, and
/// * transitive, `a < b` and `b < c` implies `a < c`. The same must hold for both `==` and `>`.
///
/// For example, while [`f64`] doesn't implement [`Ord`] because `NaN != NaN`, we can use
/// `partial_cmp` as our sort function when we know the slice doesn't contain a `NaN`.
///
/// ```
/// let mut floats = [5f64, 4.0, 1.0, 3.0, 2.0];
/// floats.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
/// assert_eq!(floats, [1.0, 2.0, 3.0, 4.0, 5.0]);
/// ```
///
/// # Current implementation
///
/// The current algorithm is based on [pattern-defeating quicksort][pdqsort] by Orson Peters,
/// which combines the fast average case of randomized quicksort with the fast worst case of
/// heapsort, while achieving linear time on slices with certain patterns. It uses some
/// randomization to avoid degenerate cases, but with a fixed seed to always provide
/// deterministic behavior.
///
/// It is typically faster than stable sorting, except in a few special cases, e.g., when the
/// slice consists of several concatenated sorted sequences.
///
/// # Examples
///
/// ```
/// let mut v = [5, 4, 1, 3, 2];
/// v.sort_unstable_by(|a, b| a.cmp(b));
/// assert!(v == [1, 2, 3, 4, 5]);
///
/// // reverse sorting
/// v.sort_unstable_by(|a, b| b.cmp(a));
/// assert!(v == [5, 4, 3, 2, 1]);
/// ```
///
/// [pdqsort]: https://github.com/orlp/pdqsort
#[inline(always)]
pub fn sort_by<T, F>(arr: &mut [T], mut compare: F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    unstable_sort(arr, |a, b| compare(a, b) == Ordering::Less);
}

// --- IMPL ---

/// Sorts `v` using pattern-defeating quicksort, which is *O*(*n* \* log(*n*)) worst-case.
#[inline(always)]
fn unstable_sort<T, F>(v: &mut [T], mut is_less: F)
where
    F: FnMut(&T, &T) -> bool,
{
    // Arrays of zero-sized types are always all-equal, and thus sorted.
    if T::IS_ZST {
        return;
    }

    // Instrumenting the standard library showed that 90+% of the calls to sort
    // by rustc are either of size 0 or 1.
    let len = v.len();
    if intrinsics::likely(len < 2) {
        return;
    }

    // More advanced sorting methods than insertion sort are faster if called in
    // a hot loop for small inputs, but for general-purpose code the small
    // binary size of insertion sort is more important. The instruction cache in
    // modern processors is very valuable, and for a single sort call in general
    // purpose code any gains from an advanced method are cancelled by i-cache
    // misses during the sort, and thrashing the i-cache for surrounding code.
    const MAX_LEN_ALWAYS_INSERTION_SORT: usize = 20;
    if intrinsics::likely(len <= MAX_LEN_ALWAYS_INSERTION_SORT) {
        insertion_sort_shift_left(v, 1, &mut is_less);
        return;
    }

    ipnsort(v, &mut is_less);
}

/// TODO explain and link explanation.
#[inline(never)]
fn ipnsort<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    let len = v.len();
    let (run_len, was_reversed) = find_existing_run(v, is_less);

    // SAFETY: find_existing_run promises to return a valid run_len.
    unsafe { intrinsics::assume(run_len <= len) };

    if run_len == len {
        if was_reversed {
            v.reverse();
        }

        // It would be possible to a do in-place merging here for a long existing streak. But that
        // makes the implementation a lot bigger, users can use `slice::sort` for that use-case.
        return;
    }

    let mut scratch = Vec::with_capacity(len);

    // Limit the number of imbalanced partitions to `2 * floor(log2(len))`.
    // The binary OR by one is used to eliminate the zero-check in the logarithm.
    let limit = 2 * (len | 1).ilog2();
    stable_quicksort(v, scratch.spare_capacity_mut(), limit, None, is_less);
}

/// Finds a run of sorted elements starting at the beginning of the slice.
///
/// Returns the length of the run, and a bool that is false when the run
/// is ascending, and true if the run strictly descending.
fn find_existing_run<T, F: FnMut(&T, &T) -> bool>(v: &[T], is_less: &mut F) -> (usize, bool) {
    let len = v.len();
    if len < 2 {
        return (len, false);
    }

    // SAFETY: We checked that len >= 2, so 0 and 1 are valid indices.
    // This also means that run_len < len implies run_len and run_len - 1
    // are valid indices as well.
    unsafe {
        let mut run_len = 2;
        let strictly_descending = is_less(v.get_unchecked(1), v.get_unchecked(0));
        if strictly_descending {
            while run_len < len && is_less(v.get_unchecked(run_len), v.get_unchecked(run_len - 1)) {
                run_len += 1;
            }
        } else {
            while run_len < len && !is_less(v.get_unchecked(run_len), v.get_unchecked(run_len - 1))
            {
                run_len += 1;
            }
        }
        (run_len, strictly_descending)
    }
}

// // #[rustc_unsafe_specialization_marker]
// trait Freeze {}

// Can the type have interior mutability, this is checked by testing if T is Freeze. If the type can
// have interior mutability it may alter itself during comparison in a way that must be observed
// after the sort operation concludes. Otherwise a type like Mutex<Option<Box<str>>> could lead to
// double free.
unsafe auto trait Freeze {}

impl<T: ?Sized> !Freeze for core::cell::UnsafeCell<T> {}
unsafe impl<T: ?Sized> Freeze for core::marker::PhantomData<T> {}
unsafe impl<T: ?Sized> Freeze for *const T {}
unsafe impl<T: ?Sized> Freeze for *mut T {}
unsafe impl<T: ?Sized> Freeze for &T {}
unsafe impl<T: ?Sized> Freeze for &mut T {}

#[const_trait]
trait IsFreeze {
    const IS_FREEZE: bool;
}

impl<T> const IsFreeze for T {
    default const IS_FREEZE: bool = false;
}

impl<T: Freeze> const IsFreeze for T {
    const IS_FREEZE: bool = true;
}

#[must_use]
const fn has_direct_interior_mutability<T>() -> bool {
    // If a type has interior mutability it may alter itself during comparison
    // in a way that must be preserved after the sort operation concludes.
    // Otherwise a type like Mutex<Option<Box<str>>> could lead to double free.
    !T::IS_FREEZE
}

// Recursively select a pseudomedian if above this threshold.
const PSEUDO_MEDIAN_REC_THRESHOLD: usize = 64;

/// Selects a pivot from `v`. Algorithm taken from glidesort by Orson Peters.
///
/// This chooses a pivot by sampling an adaptive amount of points, approximating
/// the quality of a median of sqrt(n) elements.
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
        let len_div_8 = len / 8;

        let a = v_base; // [0, floor(n/8))
        let b = v_base.add(len_div_8 * 4); // [4*floor(n/8), 5*floor(n/8))
        let c = v_base.add(len_div_8 * 7); // [7*floor(n/8), 8*floor(n/8))

        if len < PSEUDO_MEDIAN_REC_THRESHOLD {
            median3(&*a, &*b, &*c, is_less).sub_ptr(v_base)
        } else {
            median3_rec(a, b, c, len_div_8, is_less).sub_ptr(v_base)
        }
    }
}

/// Calculates an approximate median of 3 elements from sections a, b, c, or
/// recursively from an approximation of each, if they're large enough. By
/// dividing the size of each section by 8 when recursing we have logarithmic
/// recursion depth and overall sample from f(n) = 3*f(n/8) -> f(n) =
/// O(n^(log(3)/log(8))) ~= O(n^0.528) elements.
///
/// SAFETY: a, b, c must point to the start of initialized regions of memory of
/// at least n elements.
unsafe fn median3_rec<T, F: FnMut(&T, &T) -> bool>(
    mut a: *const T,
    mut b: *const T,
    mut c: *const T,
    n: usize,
    is_less: &mut F,
) -> *const T {
    // SAFETY: a, b, c still point to initialized regions of n / 8 elements,
    // by the exact same logic as in choose_pivot.
    unsafe {
        if n * 8 >= PSEUDO_MEDIAN_REC_THRESHOLD {
            let n8 = n / 8;
            a = median3_rec(a, a.add(n8 * 4), a.add(n8 * 7), n8, is_less);
            b = median3_rec(b, b.add(n8 * 4), b.add(n8 * 7), n8, is_less);
            c = median3_rec(c, c.add(n8 * 4), c.add(n8 * 7), n8, is_less);
        }
        median3(&*a, &*b, &*c, is_less)
    }
}

/// Calculates the median of 3 elements.
///
/// SAFETY: a, b, c must be valid initialized elements.
#[inline(always)]
fn median3<T, F: FnMut(&T, &T) -> bool>(a: &T, b: &T, c: &T, is_less: &mut F) -> *const T {
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

/// Sorts `v` recursively using quicksort.
///
/// `limit` when initialized with `c*log(v.len())` for some c ensures we do not
/// overflow the stack or go quadratic.
#[inline(never)]
pub fn stable_quicksort<T, F: FnMut(&T, &T) -> bool>(
    mut v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    mut limit: u32,
    mut left_ancestor_pivot: Option<&T>,
    is_less: &mut F,
) {
    loop {
        if v.len() <= T::small_sort_threshold() {
            T::small_sort(v, is_less);
            return;
        }

        // If too many bad pivot choices were made, simply fall back to heapsort in order to
        // guarantee `O(N x log(N))` worst-case.
        if limit == 0 {
            heapsort(v, is_less);
            return;
        }

        limit -= 1;

        let pivot_pos = choose_pivot(v, is_less);
        // SAFETY: choose_pivot promises to return a valid pivot index.
        unsafe {
            intrinsics::assume(pivot_pos < v.len());
        }

        // SAFETY: We only access the temporary copy for Freeze types, otherwise
        // self-modifications via `is_less` would not be observed and this would
        // be unsound. Our temporary copy does not escape this scope.
        let pivot_copy = unsafe { ManuallyDrop::new(ptr::read(&v[pivot_pos])) };
        let pivot_ref = (!has_direct_interior_mutability::<T>()).then_some(&*pivot_copy);

        // We choose a pivot, and check if this pivot is equal to our left
        // ancestor. If true, we do a partition putting equal elements on the
        // left and do not recurse on it. This gives O(n log k) sorting for k
        // distinct values, a strategy borrowed from pdqsort. For types with
        // interior mutability we can't soundly create a temporary copy of the
        // ancestor pivot, and use left_partition_len == 0 as our method for
        // detecting when we re-use a pivot, which means we do at most three
        // partition operations with pivot p instead of the optimal two.
        let mut perform_equal_partition = false;
        if let Some(la_pivot) = left_ancestor_pivot {
            perform_equal_partition = !is_less(la_pivot, &v[pivot_pos]);
        }

        let mut left_partition_len = 0;
        if !perform_equal_partition {
            left_partition_len = stable_partition(v, scratch, pivot_pos, false, is_less);
            perform_equal_partition = left_partition_len == 0;
        }

        if perform_equal_partition {
            let mid_eq = stable_partition(v, scratch, pivot_pos, true, &mut |a, b| !is_less(b, a));
            v = &mut v[mid_eq..];
            left_ancestor_pivot = None;
            continue;
        }

        // Process left side with the next loop iter, right side with recursion.
        let (left, right) = v.split_at_mut(left_partition_len);
        stable_quicksort(right, scratch, limit, pivot_ref, is_less);
        v = left;
    }
}

/// Partitions `v` using pivot `p = v[pivot_pos]` and returns the number of
/// elements less than `p`. The relative order of elements that compare < p and
/// those that compare >= p is preserved - it is a stable partition.
///
/// If `is_less` is not a strict total order or panics, `scratch.len() < v.len()`,
/// or `pivot_pos >= v.len()`, the result and `v`'s state is sound but unspecified.
fn stable_partition<T, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    pivot_pos: usize,
    pivot_goes_left: bool,
    is_less: &mut F,
) -> usize {
    let len = v.len();

    if intrinsics::unlikely(scratch.len() < len || pivot_pos >= len) {
        core::intrinsics::abort()
    }

    let v_base = v.as_ptr();
    let scratch_base = MaybeUninit::slice_as_mut_ptr(scratch);

    // The core idea is to write the values that compare as less-than to the left
    // side of `scratch`, while the values that compared as greater or equal than
    // `v[pivot_pos]` go to the right side of `scratch` in reverse. See
    // PartitionState for details.

    // SAFETY: see individual comments.
    unsafe {
        // SAFETY: we made sure the scratch has length >= len and that pivot_pos
        // is in-bounds. v and scratch are disjoint slices.
        let pivot = v_base.add(pivot_pos);
        let mut state = PartitionState::new(v_base, scratch_base, len);

        let mut pivot_in_scratch = ptr::null_mut();
        let mut loop_end_pos = pivot_pos;

        // SAFETY: this loop is equivalent to calling state.partition_one
        // exactly len times.
        loop {
            // Ideally the outer loop won't be unrolled, to save binary size,
            // but we do want the inner loop to be unrolled for small types, as
            // this gave significant performance boosts in benchmarks. Unrolling
            // through for _ in 0..UNROLL_LEN { .. } instead of manually improves
            // compile times but has a ~10-20% performance penalty on opt-level=s.
            if const { mem::size_of::<T>() <= 16 } {
                const UNROLL_LEN: usize = 4;
                let unroll_end = v_base.add(loop_end_pos.saturating_sub(UNROLL_LEN - 1));
                while state.scan < unroll_end {
                    state.partition_one(is_less(&*state.scan, &*pivot));
                    state.partition_one(is_less(&*state.scan, &*pivot));
                    state.partition_one(is_less(&*state.scan, &*pivot));
                    state.partition_one(is_less(&*state.scan, &*pivot));
                }
            }

            let loop_end = v_base.add(loop_end_pos);
            while state.scan < loop_end {
                state.partition_one(is_less(&*state.scan, &*pivot));
            }

            if loop_end_pos == len {
                break;
            }

            // We avoid comparing pivot with itself, as this could create deadlocks for
            // certain comparison operators. We also store its location later for later.
            pivot_in_scratch = state.partition_one(pivot_goes_left);

            loop_end_pos = len;
        }

        // `pivot` must be copied into its correct position again, because a
        // comparison operator might have modified it.
        if has_direct_interior_mutability::<T>() {
            ptr::copy_nonoverlapping(pivot, pivot_in_scratch, 1);
        }

        // SAFETY: partition_one being called exactly len times guarantees that scratch
        // is initialized with a permuted copy of `v`, and that num_left <= v.len().
        // Copying scratch[0..num_left] and scratch[num_left..v.len()] back is thus
        // sound, as the values in scratch will never be read again, meaning our copies
        // semantically act as moves, permuting `v`.

        // Copy all the elements < p directly from swap to v.
        let v_base = v.as_mut_ptr();
        ptr::copy_nonoverlapping(scratch_base, v_base, state.num_left);

        // Copy the elements >= p in reverse order.
        for i in 0..len - state.num_left {
            ptr::copy_nonoverlapping(
                scratch_base.add(len - 1 - i),
                v_base.add(state.num_left + i),
                1,
            );
        }

        state.num_left
    }
}

struct PartitionState<T> {
    // The start of the scratch auxiliary memory.
    scratch_base: *mut T,
    // The current element that is being looked at, scans left to right through slice.
    scan: *const T,
    // Counts the number of elements that went to the left side, also works around:
    // https://github.com/rust-lang/rust/issues/117128
    num_left: usize,
    // Reverse scratch output pointer.
    scratch_rev: *mut T,
}

impl<T> PartitionState<T> {
    /// # Safety
    /// scan and scratch must point to valid disjoint buffers of length len. The
    /// scan buffer must be initialized.
    unsafe fn new(scan: *const T, scratch: *mut T, len: usize) -> Self {
        Self {
            scratch_base: scratch,
            scan,
            num_left: 0,
            scratch_rev: scratch.add(len),
        }
    }

    /// Depending on the value of `towards_left` this function will write a value
    /// to the growing left or right side of the scratch memory. This forms the
    /// branchless core of the partition.
    ///
    /// # Safety
    /// This function may be called at most `len` times. If it is called exactly
    /// `len` times the scratch buffer then contains a copy of each element from
    /// the scan buffer exactly once - a permutation, and num_left <= len.
    unsafe fn partition_one(&mut self, towards_left: bool) -> *mut T {
        // SAFETY: see individual comments.
        unsafe {
            // SAFETY: in-bounds because this function is called at most len times, and thus
            // right now is incremented at most len - 1 times. Similarly, num_left < len and
            // num_right < len, where num_right == i - num_left at the start of the ith
            // iteration (zero-indexed).
            self.scratch_rev = self.scratch_rev.sub(1);

            // SAFETY: now we have scratch_rev == base + len - (i + 1). This means
            // scratch_rev + num_left == base + len - 1 - num_right < base + len.
            let dst_base = if towards_left {
                self.scratch_base
            } else {
                self.scratch_rev
            };
            let dst = dst_base.add(self.num_left);
            ptr::copy_nonoverlapping(self.scan, dst, 1);

            self.num_left += towards_left as usize;
            self.scan = self.scan.add(1);
            dst
        }
    }
}

/// Using a trait allows us to specialize on `Freeze` which in turn allows us to make safe
/// abstractions.
pub(crate) trait UnstableSmallSortTypeImpl: Sized {
    /// For which input length <= return value of this function, is it valid to call `small_sort`.
    fn small_sort_threshold() -> usize;

    /// Sorts `v` using strategies optimized for small sizes.
    fn small_sort<F: FnMut(&Self, &Self) -> bool>(v: &mut [Self], is_less: &mut F);
}

impl<T> UnstableSmallSortTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        SMALL_SORT_FALLBACK_THRESHOLD
    }

    #[inline(always)]
    default fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        small_sort_fallback(v, is_less);
    }
}

impl<T: Freeze> UnstableSmallSortTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        match const { choose_unstable_small_sort::<T>() } {
            UnstalbeSmallSort::Fallback => SMALL_SORT_FALLBACK_THRESHOLD,
            UnstalbeSmallSort::General => SMALL_SORT_GENERAL_THRESHOLD,
            UnstalbeSmallSort::Network => SMALL_SORT_NETWORK_THRESHOLD,
        }
    }

    #[inline(always)]
    fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        // This construct is used to limit the LLVM IR generated, which saves large amounts of
        // compile-time by only instantiating the code that is needed. Idea by Frank Steffahn.
        (const { inst_unstable_small_sort::<T, F>() })(v, is_less);
    }
}

/// Optimal number of comparisons, and good perf.
const SMALL_SORT_FALLBACK_THRESHOLD: usize = 16;

/// SAFETY: If you change this value, you have to adjust [`small_sort_general`] !
const SMALL_SORT_GENERAL_THRESHOLD: usize = 32;

/// [`small_sort_general`] uses [`sort8_stable`] as primitive and does a kind of ping-pong merge,
/// where the output of the first two [`sort8_stable`] calls is stored at the end of the scratch
/// buffer. This simplifies panic handling and avoids additional copies. This affects the required
/// scratch buffer size.
///
/// SAFETY: If you change this value, you have to adjust [`small_sort_general`] !
const SMALL_SORT_GENERAL_SCRATCH_LEN: usize = SMALL_SORT_GENERAL_THRESHOLD + 16;

/// SAFETY: If you change this value, you have to adjust [`small_sort_network`] !
const SMALL_SORT_NETWORK_THRESHOLD: usize = 32;
const SMALL_SORT_NETWORK_SCRATCH_LEN: usize = SMALL_SORT_NETWORK_THRESHOLD;

/// Using a stack array, could cause a stack overflow if the type `T` is very large. To be
/// conservative we limit the usage of small-sorts that require a stack array to types that fit
/// within this limit.
const MAX_STACK_ARRAY_SIZE: usize = 4096;

enum UnstalbeSmallSort {
    Fallback,
    General,
    Network,
}

const fn choose_unstable_small_sort<T: Freeze>() -> UnstalbeSmallSort {
    if T::IS_COPY
        && has_efficient_in_place_swap::<T>()
        && (mem::size_of::<T>() * SMALL_SORT_NETWORK_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE
    {
        // Heuristic for int like types.
        return UnstalbeSmallSort::Network;
    }

    if (mem::size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
        return UnstalbeSmallSort::General;
    }

    UnstalbeSmallSort::Fallback
}

const fn inst_unstable_small_sort<T: Freeze, F: FnMut(&T, &T) -> bool>() -> fn(&mut [T], &mut F) {
    match const { choose_unstable_small_sort::<T>() } {
        UnstalbeSmallSort::Fallback => small_sort_fallback::<T, F>,
        UnstalbeSmallSort::General => small_sort_general::<T, F>,
        UnstalbeSmallSort::Network => small_sort_network::<T, F>,
    }
}

fn small_sort_fallback<T, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F) {
    if v.len() >= 2 {
        insertion_sort_shift_left(v, 1, is_less);
    }
}

fn small_sort_general<T: Freeze, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F) {
    let mut stack_array = MaybeUninit::<[T; SMALL_SORT_GENERAL_SCRATCH_LEN]>::uninit();

    let scratch = unsafe {
        slice::from_raw_parts_mut(
            stack_array.as_mut_ptr() as *mut MaybeUninit<T>,
            SMALL_SORT_GENERAL_SCRATCH_LEN,
        )
    };

    small_sort_general_with_scratch(v, scratch, is_less);
}

fn small_sort_general_with_scratch<T: Freeze, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    is_less: &mut F,
) {
    let len = v.len();
    if len < 2 {
        return;
    }

    if scratch.len() < len + 16 {
        intrinsics::abort();
    }

    let v_base = v.as_mut_ptr();
    let len_div_2 = len / 2;

    // SAFETY: See individual comments.
    unsafe {
        let scratch_base = scratch.as_mut_ptr() as *mut T;

        let presorted_len = if const { mem::size_of::<T>() <= 16 } && len >= 16 {
            // SAFETY: scratch_base is valid and has enough space.
            sort8_stable(v_base, scratch_base, scratch_base.add(len), is_less);
            sort8_stable(
                v_base.add(len_div_2),
                scratch_base.add(len_div_2),
                scratch_base.add(len + 8),
                is_less,
            );

            8
        } else if len >= 8 {
            // SAFETY: scratch_base is valid and has enough space.
            sort4_stable(v_base, scratch_base, is_less);
            sort4_stable(v_base.add(len_div_2), scratch_base.add(len_div_2), is_less);

            4
        } else {
            ptr::copy_nonoverlapping(v_base, scratch_base, 1);
            ptr::copy_nonoverlapping(v_base.add(len_div_2), scratch_base.add(len_div_2), 1);

            1
        };

        for offset in [0, len_div_2] {
            // SAFETY: at this point dst is initialized with presorted_len elements.
            // We extend this to desired_len, src is valid for desired_len elements.
            let src = v_base.add(offset);
            let dst = scratch_base.add(offset);
            let desired_len = if offset == 0 {
                len_div_2
            } else {
                len - len_div_2
            };

            for i in presorted_len..desired_len {
                ptr::copy_nonoverlapping(src.add(i), dst.add(i), 1);
                insert_tail(dst, dst.add(i), is_less);
            }
        }

        // SAFETY: see comment in `CopyOnDrop::drop`.
        let drop_guard = CopyOnDrop {
            src: scratch_base,
            dst: v_base,
            len,
        };

        // SAFETY: at this point scratch_base is fully initialized, allowing us
        // to use it as the source of our merge back into the original array.
        // If a panic occurs we ensure the original array is restored to a valid
        // permutation of the input through drop_guard. This technique is similar
        // to ping-pong merging.
        bidirectional_merge(
            &*ptr::slice_from_raw_parts(drop_guard.src, drop_guard.len),
            drop_guard.dst,
            is_less,
        );
        mem::forget(drop_guard);
    }
}

struct CopyOnDrop<T> {
    src: *const T,
    dst: *mut T,
    len: usize,
}

impl<T> Drop for CopyOnDrop<T> {
    fn drop(&mut self) {
        // SAFETY: `src` must contain `len` initialized elements, and dst must
        // be valid to write `len` elements.
        unsafe {
            ptr::copy_nonoverlapping(self.src, self.dst, self.len);
        }
    }
}

fn small_sort_network<T, F>(v: &mut [T], is_less: &mut F)
where
    T: Freeze,
    F: FnMut(&T, &T) -> bool,
{
    // This implementation is tuned to be efficient for integer types.

    let len = v.len();
    if len < 2 {
        return;
    }

    if len > SMALL_SORT_NETWORK_SCRATCH_LEN {
        intrinsics::abort();
    }

    let mut stack_array = MaybeUninit::<[T; SMALL_SORT_NETWORK_SCRATCH_LEN]>::uninit();

    let len_div_2 = len / 2;
    let no_merge = len < 18;

    let v_base = v.as_mut_ptr();
    let initial_region_len = if no_merge { len } else { len_div_2 };
    // SAFETY: Both possible values of `initial_region_len` are in-bounds.
    let mut region = unsafe { &mut *ptr::slice_from_raw_parts_mut(v_base, initial_region_len) };

    // Avoid compiler unrolling, we *really* don't want that to happen here for binary-size reasons.
    loop {
        let presorted_len = if region.len() >= 13 {
            sort13_optimal(region, is_less);
            13
        } else if region.len() >= 9 {
            sort9_optimal(region, is_less);
            9
        } else {
            1
        };

        insertion_sort_shift_left(region, presorted_len, is_less);

        if no_merge {
            return;
        }

        if region.as_ptr() != v_base {
            break;
        }

        // SAFETY: The right side of `v` based on `len_div_2` is guaranteed in-bounds.
        region =
            unsafe { &mut *ptr::slice_from_raw_parts_mut(v_base.add(len_div_2), len - len_div_2) };
    }

    // SAFETY: We checked that T is Freeze and thus observation safe.
    // Should is_less panic v was not modified in parity_merge and retains it's original input.
    // scratch and v must not alias and scratch has v.len() space.
    unsafe {
        let scratch_base = stack_array.as_mut_ptr() as *mut T;
        bidirectional_merge(
            &mut *ptr::slice_from_raw_parts_mut(v_base, len),
            scratch_base,
            is_less,
        );
        ptr::copy_nonoverlapping(scratch_base, v_base, len);
    }
}

/// Swap two values in the slice pointed to by `v_base` at the position `a_pos` and `b_pos` if the
/// value at position `b_pos` is less than the one at position `a_pos`.
pub unsafe fn swap_if_less<T, F>(v_base: *mut T, a_pos: usize, b_pos: usize, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: the caller must guarantee that `a` and `b` each added to `v_base` yield valid
    // pointers into `v_base`, and are properly aligned, and part of the same allocation.

    let v_a = v_base.add(a_pos);
    let v_b = v_base.add(b_pos);

    // PANIC SAFETY: if is_less panics, no scratch memory was created and the slice should still be
    // in a well defined state, without duplicates.

    // Important to only swap if it is more and not if it is equal. is_less should return false for
    // equal, so we don't swap.
    let should_swap = is_less(&*v_b, &*v_a);

    // This is a branchless version of swap if.
    // The equivalent code with a branch would be:
    //
    // if should_swap {
    //     ptr::swap(left, right, 1);
    // }

    // The goal is to generate cmov instructions here.
    let left_swap = if should_swap { v_b } else { v_a };
    let right_swap = if should_swap { v_a } else { v_b };

    let right_swap_tmp = ManuallyDrop::new(ptr::read(right_swap));
    ptr::copy(left_swap, v_a, 1);
    ptr::copy_nonoverlapping(&*right_swap_tmp, v_b, 1);
}

// Never inline this function to avoid code bloat. It still optimizes nicely and has practically no
// performance impact.
fn sort9_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: caller must ensure v.len() >= 9.
    if v.len() < 9 {
        intrinsics::abort();
    }

    let v_base = v.as_mut_ptr();

    // Optimal sorting network see:
    // https://bertdobbelaere.github.io/sorting_networks.html.

    // SAFETY: We checked the len.
    unsafe {
        swap_if_less(v_base, 0, 3, is_less);
        swap_if_less(v_base, 1, 7, is_less);
        swap_if_less(v_base, 2, 5, is_less);
        swap_if_less(v_base, 4, 8, is_less);
        swap_if_less(v_base, 0, 7, is_less);
        swap_if_less(v_base, 2, 4, is_less);
        swap_if_less(v_base, 3, 8, is_less);
        swap_if_less(v_base, 5, 6, is_less);
        swap_if_less(v_base, 0, 2, is_less);
        swap_if_less(v_base, 1, 3, is_less);
        swap_if_less(v_base, 4, 5, is_less);
        swap_if_less(v_base, 7, 8, is_less);
        swap_if_less(v_base, 1, 4, is_less);
        swap_if_less(v_base, 3, 6, is_less);
        swap_if_less(v_base, 5, 7, is_less);
        swap_if_less(v_base, 0, 1, is_less);
        swap_if_less(v_base, 2, 4, is_less);
        swap_if_less(v_base, 3, 5, is_less);
        swap_if_less(v_base, 6, 8, is_less);
        swap_if_less(v_base, 2, 3, is_less);
        swap_if_less(v_base, 4, 5, is_less);
        swap_if_less(v_base, 6, 7, is_less);
        swap_if_less(v_base, 1, 2, is_less);
        swap_if_less(v_base, 3, 4, is_less);
        swap_if_less(v_base, 5, 6, is_less);
    }
}

// Never inline this function to avoid code bloat. It still optimizes nicely and has practically no
// performance impact.
fn sort13_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: caller must ensure v.len() >= 13.
    if v.len() < 13 {
        intrinsics::abort();
    }

    let v_base = v.as_mut_ptr();

    // Optimal sorting network see:
    // https://bertdobbelaere.github.io/sorting_networks.html.

    // SAFETY: We checked the len.
    unsafe {
        swap_if_less(v_base, 0, 12, is_less);
        swap_if_less(v_base, 1, 10, is_less);
        swap_if_less(v_base, 2, 9, is_less);
        swap_if_less(v_base, 3, 7, is_less);
        swap_if_less(v_base, 5, 11, is_less);
        swap_if_less(v_base, 6, 8, is_less);
        swap_if_less(v_base, 1, 6, is_less);
        swap_if_less(v_base, 2, 3, is_less);
        swap_if_less(v_base, 4, 11, is_less);
        swap_if_less(v_base, 7, 9, is_less);
        swap_if_less(v_base, 8, 10, is_less);
        swap_if_less(v_base, 0, 4, is_less);
        swap_if_less(v_base, 1, 2, is_less);
        swap_if_less(v_base, 3, 6, is_less);
        swap_if_less(v_base, 7, 8, is_less);
        swap_if_less(v_base, 9, 10, is_less);
        swap_if_less(v_base, 11, 12, is_less);
        swap_if_less(v_base, 4, 6, is_less);
        swap_if_less(v_base, 5, 9, is_less);
        swap_if_less(v_base, 8, 11, is_less);
        swap_if_less(v_base, 10, 12, is_less);
        swap_if_less(v_base, 0, 5, is_less);
        swap_if_less(v_base, 3, 8, is_less);
        swap_if_less(v_base, 4, 7, is_less);
        swap_if_less(v_base, 6, 11, is_less);
        swap_if_less(v_base, 9, 10, is_less);
        swap_if_less(v_base, 0, 1, is_less);
        swap_if_less(v_base, 2, 5, is_less);
        swap_if_less(v_base, 6, 9, is_less);
        swap_if_less(v_base, 7, 8, is_less);
        swap_if_less(v_base, 10, 11, is_less);
        swap_if_less(v_base, 1, 3, is_less);
        swap_if_less(v_base, 2, 4, is_less);
        swap_if_less(v_base, 5, 6, is_less);
        swap_if_less(v_base, 9, 10, is_less);
        swap_if_less(v_base, 1, 2, is_less);
        swap_if_less(v_base, 3, 4, is_less);
        swap_if_less(v_base, 5, 7, is_less);
        swap_if_less(v_base, 6, 8, is_less);
        swap_if_less(v_base, 2, 3, is_less);
        swap_if_less(v_base, 4, 5, is_less);
        swap_if_less(v_base, 6, 7, is_less);
        swap_if_less(v_base, 8, 9, is_less);
        swap_if_less(v_base, 3, 4, is_less);
        swap_if_less(v_base, 5, 6, is_less);
    }
}

/// Sorts range [begin, tail] assuming [begin, tail) is already sorted.
///
/// # Safety
/// begin < tail and p must be valid and initialized for all begin <= p <= tail.
unsafe fn insert_tail<T, F: FnMut(&T, &T) -> bool>(begin: *mut T, tail: *mut T, is_less: &mut F) {
    // SAFETY: see individual comments.
    unsafe {
        // SAFETY: in-bounds as tail > begin.
        let mut sift = tail.sub(1);
        if !is_less(&*tail, &*sift) {
            return;
        }

        // SAFETY: after this read tail is never read from again, as we only ever
        // read from sift, sift < tail and we only ever decrease sift. Thus this is
        // effectively a move, not a copy. Should a panic occur, or we have found
        // the correct insertion position, gap_guard ensures the element is moved
        // back into the array.
        let tmp = ManuallyDrop::new(tail.read());
        let mut gap_guard = CopyOnDrop {
            src: &*tmp,
            dst: tail,
            len: 1,
        };

        loop {
            // SAFETY: we move sift into the gap (which is valid), and point the
            // gap guard destination at sift, ensuring that if a panic occurs the
            // gap is once again filled.
            ptr::copy_nonoverlapping(sift, gap_guard.dst, 1);
            gap_guard.dst = sift;

            if sift == begin {
                break;
            }

            // SAFETY: we checked that sift != begin, thus this is in-bounds.
            sift = sift.sub(1);
            if !is_less(&tmp, &*sift) {
                break;
            }
        }
    }
}

/// Sort `v` assuming `v[..offset]` is already sorted.
pub fn insertion_sort_shift_left<T, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    offset: usize,
    is_less: &mut F,
) {
    let len = v.len();
    if offset == 0 || offset > len {
        intrinsics::abort();
    }

    // SAFETY: see individual comments.
    unsafe {
        // We write this basic loop directly using pointers, as when we use a
        // for loop LLVM likes to unroll this loop which we do not want.
        // SAFETY: v_end is the one-past-end pointer, and we checked that
        // offset <= len, thus tail is also in-bounds.
        let v_base = v.as_mut_ptr();
        let v_end = v_base.add(len);
        let mut tail = v_base.add(offset);
        while tail != v_end {
            // SAFETY: v_base and tail are both valid pointers to elements, and
            // v_base < tail since we checked offset != 0.
            insert_tail(v_base, tail, is_less);

            // SAFETY: we checked that tail is not yet the one-past-end pointer.
            tail = tail.add(1);
        }
    }
}

/// SAFETY: The caller MUST guarantee that `v_base` is valid for 4 reads and
/// `dst` is valid for 4 writes. The result will be stored in `dst[0..4]`.
pub unsafe fn sort4_stable<T, F: FnMut(&T, &T) -> bool>(
    v_base: *const T,
    dst: *mut T,
    is_less: &mut F,
) {
    // By limiting select to picking pointers, we are guaranteed good cmov code-gen
    // regardless of type T's size. Further this only does 5 instead of 6
    // comparisons compared to a stable transposition 4 element sorting-network,
    // and always copies each element exactly once.

    // SAFETY: all pointers have offset at most 3 from v_base and dst, and are
    // thus in-bounds by the precondition.
    unsafe {
        // Stably create two pairs a <= b and c <= d.
        let c1 = is_less(&*v_base.add(1), &*v_base);
        let c2 = is_less(&*v_base.add(3), &*v_base.add(2));
        let a = v_base.add(c1 as usize);
        let b = v_base.add(!c1 as usize);
        let c = v_base.add(2 + c2 as usize);
        let d = v_base.add(2 + (!c2 as usize));

        // Compare (a, c) and (b, d) to identify max/min. We're left with two
        // unknown elements, but because we are a stable sort we must know which
        // one is leftmost and which one is rightmost.
        // c3, c4 | min max unknown_left unknown_right
        //  0,  0 |  a   d    b         c
        //  0,  1 |  a   b    c         d
        //  1,  0 |  c   d    a         b
        //  1,  1 |  c   b    a         d
        let c3 = is_less(&*c, &*a);
        let c4 = is_less(&*d, &*b);
        let min = select(c3, c, a);
        let max = select(c4, b, d);
        let unknown_left = select(c3, a, select(c4, c, b));
        let unknown_right = select(c4, d, select(c3, b, c));

        // Sort the last two unknown elements.
        let c5 = is_less(&*unknown_right, &*unknown_left);
        let lo = select(c5, unknown_right, unknown_left);
        let hi = select(c5, unknown_left, unknown_right);

        ptr::copy_nonoverlapping(min, dst, 1);
        ptr::copy_nonoverlapping(lo, dst.add(1), 1);
        ptr::copy_nonoverlapping(hi, dst.add(2), 1);
        ptr::copy_nonoverlapping(max, dst.add(3), 1);
    }

    #[inline(always)]
    fn select<T>(cond: bool, if_true: *const T, if_false: *const T) -> *const T {
        if cond {
            if_true
        } else {
            if_false
        }
    }
}

/// SAFETY: The caller MUST guarantee that `v_base` is valid for 8 reads and
/// writes, `scratch_base` and `dst` MUST be valid for 8 writes. The result will
/// be stored in `dst[0..8]`.
unsafe fn sort8_stable<T: Freeze, F: FnMut(&T, &T) -> bool>(
    v_base: *mut T,
    dst: *mut T,
    scratch_base: *mut T,
    is_less: &mut F,
) {
    // SAFETY: these pointers are all in-bounds by the precondition of our function.
    unsafe {
        sort4_stable(v_base, scratch_base, is_less);
        sort4_stable(v_base.add(4), scratch_base.add(4), is_less);
    }

    // SAFETY: scratch_base[0..8] is now initialized, allowing us to merge back
    // into dst.
    unsafe {
        bidirectional_merge(&*ptr::slice_from_raw_parts(scratch_base, 8), dst, is_less);
    }
}

#[inline(always)]
unsafe fn merge_up<T, F: FnMut(&T, &T) -> bool>(
    mut left_src: *const T,
    mut right_src: *const T,
    mut dst: *mut T,
    is_less: &mut F,
) -> (*const T, *const T, *mut T) {
    // This is a branchless merge utility function.
    // The equivalent code with a branch would be:
    //
    // if !is_less(&*right_src, &*left_src) {
    //     ptr::copy_nonoverlapping(left_src, dst, 1);
    //     left_src = left_src.add(1);
    // } else {
    //     ptr::copy_nonoverlapping(right_src, dst, 1);
    //     right_src = right_src.add(1);
    // }
    // dst = dst.add(1);

    // SAFETY: The caller must guarantee that `left_src`, `right_src` are valid
    // to read and `dst` is valid to write, while not aliasing.
    unsafe {
        let is_l = !is_less(&*right_src, &*left_src);
        let src = if is_l { left_src } else { right_src };
        ptr::copy_nonoverlapping(src, dst, 1);
        right_src = right_src.add(!is_l as usize);
        left_src = left_src.add(is_l as usize);
        dst = dst.add(1);
    }

    (left_src, right_src, dst)
}

#[inline(always)]
unsafe fn merge_down<T, F: FnMut(&T, &T) -> bool>(
    mut left_src: *const T,
    mut right_src: *const T,
    mut dst: *mut T,
    is_less: &mut F,
) -> (*const T, *const T, *mut T) {
    // This is a branchless merge utility function.
    // The equivalent code with a branch would be:
    //
    // if !is_less(&*right_src, &*left_src) {
    //     ptr::copy_nonoverlapping(right_src, dst, 1);
    //     right_src = right_src.wrapping_sub(1);
    // } else {
    //     ptr::copy_nonoverlapping(left_src, dst, 1);
    //     left_src = left_src.wrapping_sub(1);
    // }
    // dst = dst.sub(1);

    // SAFETY: The caller must guarantee that `left_src`, `right_src` are valid
    // to read and `dst` is valid to write, while not aliasing.
    unsafe {
        let is_l = !is_less(&*right_src, &*left_src);
        let src = if is_l { right_src } else { left_src };
        ptr::copy_nonoverlapping(src, dst, 1);
        right_src = right_src.wrapping_sub(is_l as usize);
        left_src = left_src.wrapping_sub(!is_l as usize);
        dst = dst.sub(1);
    }

    (left_src, right_src, dst)
}

/// Merge v assuming v[..len / 2] and v[len / 2..] are sorted.
///
/// Original idea for bi-directional merging by Igor van den Hoven (quadsort),
/// adapted to only use merge up and down. In contrast to the original
/// parity_merge function, it performs 2 writes instead of 4 per iteration.
///
/// # Safety
/// The caller must guarantee that `dst` is valid for v.len() writes.
/// Also `v.as_ptr()` and `dst` must not alias and v.len() must be >= 2.
///
/// Note that T must be Freeze, the comparison function is evaluated on outdated
/// temporary 'copies' that may not end up in the final array.
unsafe fn bidirectional_merge<T: Freeze, F: FnMut(&T, &T) -> bool>(
    v: &[T],
    dst: *mut T,
    is_less: &mut F,
) {
    // It helps to visualize the merge:
    //
    // Initial:
    //
    //  |dst (in dst)
    //  |left               |right
    //  v                   v
    // [xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx]
    //                     ^                   ^
    //                     |left_rev           |right_rev
    //                                         |dst_rev (in dst)
    //
    // After:
    //
    //                      |dst (in dst)
    //        |left         |           |right
    //        v             v           v
    // [xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx]
    //       ^             ^           ^
    //       |left_rev     |           |right_rev
    //                     |dst_rev (in dst)
    //
    // In each iteration one of left or right moves up one position, and one of
    // left_rev or right_rev moves down one position, whereas dst always moves
    // up one position and dst_rev always moves down one position. Assuming
    // the input was sorted and the comparison function is correctly implemented
    // at the end we will have left == left_rev + 1, and right == right_rev + 1,
    // fully consuming the input having written it to dst.

    let len = v.len();
    let src = v.as_ptr();

    let len_div_2 = len / 2;
    intrinsics::assume(len_div_2 != 0); // This can avoid useless code-gen.

    // SAFETY: no matter what the result of the user-provided comparison function
    // is, all 4 read pointers will always be in-bounds. Writing `dst` and `dst_rev`
    // will always be in bounds if the caller guarantees that `dst` is valid for
    // `v.len()` writes.
    unsafe {
        let mut left = src;
        let mut right = src.add(len_div_2);
        let mut dst = dst;

        let mut left_rev = src.add(len_div_2 - 1);
        let mut right_rev = src.add(len - 1);
        let mut dst_rev = dst.add(len - 1);

        for _ in 0..len_div_2 {
            (left, right, dst) = merge_up(left, right, dst, is_less);
            (left_rev, right_rev, dst_rev) = merge_down(left_rev, right_rev, dst_rev, is_less);
        }

        let left_end = left_rev.wrapping_add(1);
        let right_end = right_rev.wrapping_add(1);

        // Odd length, so one element is left unconsumed in the input.
        if len % 2 != 0 {
            let left_nonempty = left < left_end;
            let last_src = if left_nonempty { left } else { right };
            ptr::copy_nonoverlapping(last_src, dst, 1);
            left = left.add(left_nonempty as usize);
            right = right.add((!left_nonempty) as usize);
        }

        // We now should have consumed the full input exactly once. This can
        // only fail if the comparison operator fails to be Ord, in which case
        // we will panic and never access the inconsistent state in dst.
        if left != left_end || right != right_end {
            panic_on_ord_violation();
        }
    }
}

#[inline(never)]
fn panic_on_ord_violation() -> ! {
    panic!("Ord violation");
}

#[must_use]
const fn has_efficient_in_place_swap<T>() -> bool {
    const MEM_SIZE_U64: usize = mem::size_of::<u64>();

    mem::size_of::<T>() <= MEM_SIZE_U64
}

#[test]
fn type_info() {
    assert!(has_efficient_in_place_swap::<i32>());
    assert!(has_efficient_in_place_swap::<u64>());
    assert!(!has_efficient_in_place_swap::<u128>());
    assert!(!has_efficient_in_place_swap::<String>());
}

trait IsCopy {
    const IS_COPY: bool;
}

impl<T> IsCopy for T {
    default const IS_COPY: bool = false;
}

impl<T: Copy> IsCopy for T {
    const IS_COPY: bool = true;
}

/// Sorts `v` using heapsort, which guarantees *O*(*n* \* log(*n*)) worst-case.
///
/// Never inline this, it sits the main hot-loop in `recurse` and is meant as unlikely algorithmic
/// fallback.
#[inline(never)]
pub(crate) fn heapsort<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    let len = v.len();

    for i in (0..len + len / 2).rev() {
        let sift_idx = if i >= len {
            i - len
        } else {
            v.swap(0, i);
            0
        };

        // SAFETY: The above calculation ensures that `sift_idx` is either 0 or
        // `(len..(len + (len / 2))) - len`, which simplifies to `0..(len / 2)`.
        // This guarantees the required `sift_idx <= len`.
        unsafe {
            sift_down(&mut v[..cmp::min(i, len)], sift_idx, is_less);
        }
    }
}

// This binary heap respects the invariant `parent >= child`.
//
// SAFETY: The caller has to guarantee that `node <= v.len()`.
#[inline(always)]
unsafe fn sift_down<T, F>(v: &mut [T], mut node: usize, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: See function safety.
    unsafe {
        intrinsics::assume(node <= v.len());
    }

    let len = v.len();

    let v_base = v.as_mut_ptr();

    loop {
        // Children of `node`.
        let mut child = 2 * node + 1;
        if child >= len {
            break;
        }

        // SAFETY: The invariants and checks guarantee that both node and child are in-bounds.
        unsafe {
            // Choose the greater child.
            if child + 1 < len {
                // We need a branch to be sure not to out-of-bounds index,
                // but it's highly predictable.  The comparison, however,
                // is better done branchless, especially for primitives.
                child += is_less(&*v_base.add(child), &*v_base.add(child + 1)) as usize;
            }

            // Stop if the invariant holds at `node`.
            if !is_less(&*v_base.add(node), &*v_base.add(child)) {
                break;
            }

            ptr::swap_nonoverlapping(v_base.add(node), v_base.add(child), 1);
        }

        node = child;
    }
}
