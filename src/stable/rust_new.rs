#![allow(unused)]

use std::cmp::Ordering;
use std::intrinsics;
use std::mem;
use std::ptr;

#[inline]
pub fn sort<T>(v: &mut [T])
where
    T: Ord,
{
    stable_sort(v, |a, b| a.lt(b));
}

#[inline]
pub fn sort_by<T, F>(v: &mut [T], mut compare: F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    stable_sort(v, |a, b| compare(a, b) == Ordering::Less);
}

////////////////////////////////////////////////////////////////////////////////
// Sorting
////////////////////////////////////////////////////////////////////////////////

#[inline]
#[cfg(not(no_global_oom_handling))]
fn stable_sort<T, F>(v: &mut [T], mut is_less: F)
where
    F: FnMut(&T, &T) -> bool,
{
    if mem::size_of::<T>() == 0 {
        // Sorting has no meaningful behavior on zero-sized types. Do nothing.
        return;
    }

    merge_sort(v, &mut is_less);
}

#[cfg(not(no_global_oom_handling))]
fn merge_sort<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // Sorting has no meaningful behavior on zero-sized types.
    if mem::size_of::<T>() == 0 {
        return;
    }

    let len = v.len();

    if len < 2 {
        return;
    }

    // Don't allocate right at the beginning, wait to see if the slice is already sorted or
    // reversed.
    let mut buf;
    let mut buf_ptr: *mut T = ptr::null_mut();

    // In order to identify natural runs in `v`, we traverse it backwards. That might seem like a
    // strange decision, but consider the fact that merges more often go in the opposite direction
    // (forwards). According to benchmarks, merging forwards is slightly faster than merging
    // backwards. To conclude, identifying runs by traversing backwards improves performance.
    let mut runs = vec![];
    let mut end = len;
    while end > 0 {
        // Find the next natural run, and reverse it if it's strictly descending.
        let mut start = end - 1;
        if start > 0 {
            start -= 1;
            unsafe {
                if is_less(v.get_unchecked(start + 1), v.get_unchecked(start)) {
                    while start > 0 && is_less(v.get_unchecked(start), v.get_unchecked(start - 1)) {
                        start -= 1;
                    }
                    v[start..end].reverse();
                } else {
                    while start > 0 && !is_less(v.get_unchecked(start), v.get_unchecked(start - 1))
                    {
                        start -= 1;
                    }
                }
            }
        }

        if start == 0 && end == len {
            // The input was either fully ascending or descending. It is now sorted and we can
            // return without allocating.
            return;
        } else if buf_ptr.is_null() {
            // Short arrays get sorted in-place via insertion sort to avoid allocations.
            if sort_small_stable(v, start, is_less) {
                return;
            }

            // Allocate a buffer to use as scratch memory. We keep the length 0 so we can keep in it
            // shallow copies of the contents of `v` without risking the dtors running on copies if
            // `is_less` panics. When merging two sorted runs, this buffer holds a copy of the
            // shorter run, which will always have length at most `len / 2`.
            buf = Vec::with_capacity(len / 2);
            buf_ptr = buf.as_mut_ptr();
        }

        // SAFETY: end > start.
        start = provide_sorted_batch(v, start, end, is_less);

        // Push this run onto the stack.
        runs.push(Run {
            start,
            len: end - start,
        });
        end = start;

        // Merge some pairs of adjacent runs to satisfy the invariants.
        while let Some(r) = collapse(&runs) {
            let left = runs[r + 1];
            let right = runs[r];
            unsafe {
                merge(
                    &mut v[left.start..right.start + right.len],
                    left.len,
                    buf_ptr,
                    is_less,
                );
            }
            runs[r] = Run {
                start: left.start,
                len: left.len + right.len,
            };
            runs.remove(r + 1);
        }
    }

    // Finally, exactly one run must remain in the stack.
    debug_assert!(runs.len() == 1 && runs[0].start == 0 && runs[0].len == len);

    // Examines the stack of runs and identifies the next pair of runs to merge. More specifically,
    // if `Some(r)` is returned, that means `runs[r]` and `runs[r + 1]` must be merged next. If the
    // algorithm should continue building a new run instead, `None` is returned.
    //
    // TimSort is infamous for its buggy implementations, as described here:
    // http://envisage-project.eu/timsort-specification-and-verification/
    //
    // The gist of the story is: we must enforce the invariants on the top four runs on the stack.
    // Enforcing them on just top three is not sufficient to ensure that the invariants will still
    // hold for *all* runs in the stack.
    //
    // This function correctly checks invariants for the top four runs. Additionally, if the top
    // run starts at index 0, it will always demand a merge operation until the stack is fully
    // collapsed, in order to complete the sort.
    #[inline]
    fn collapse(runs: &[Run]) -> Option<usize> {
        let n = runs.len();
        if n >= 2
            && (runs[n - 1].start == 0
                || runs[n - 2].len <= runs[n - 1].len
                || (n >= 3 && runs[n - 3].len <= runs[n - 2].len + runs[n - 1].len)
                || (n >= 4 && runs[n - 4].len <= runs[n - 3].len + runs[n - 2].len))
        {
            if n >= 3 && runs[n - 3].len < runs[n - 1].len {
                Some(n - 3)
            } else {
                Some(n - 2)
            }
        } else {
            None
        }
    }

    #[derive(Clone, Copy)]
    struct Run {
        len: usize,
        start: usize,
    }
}

/// Check whether `v` applies for small sort optimization.
/// `v[start..]` is assumed already sorted.
fn sort_small_stable<T, F>(v: &mut [T], start: usize, is_less: &mut F) -> bool
where
    F: FnMut(&T, &T) -> bool,
{
    let len = v.len();

    if qualifies_for_branchless_sort::<T>() {
        // Testing showed that even though this incurs more comparisons, up to size 32 (4 * 8),
        // avoiding the allocation and sticking with simple code is worth it. Going further eg. 40
        // is still worth it for u64 or even types with more expensive comparisons, but risks
        // incurring just too many comparisons than doing the regular TimSort.
        const MAX_NO_ALLOC_SIZE: usize = 32;
        if len <= MAX_NO_ALLOC_SIZE {
            if len < 8 {
                insertion_sort_shift_right(v, start, is_less);
                return true;
            }

            let mut merge_count = 0;
            for chunk in v.chunks_exact_mut(8) {
                // SAFETY: chunks_exact_mut promised to give us slices of len 8.
                unsafe {
                    sort8_stable(chunk, is_less);
                }
                merge_count += 1;
            }

            let mut swap = mem::MaybeUninit::<[T; 8]>::uninit();
            let swap_ptr = swap.as_mut_ptr() as *mut T;

            let mut i = 8;
            while merge_count > 1 {
                // SAFETY: We know the smaller side will be of size 8 because mid is 8. And both
                // sides are non empty because of merge_count, and the right side will always be of
                // size 8 and the left size of 8 or greater. Thus the smaller side will always be
                // exactly 8 long, the size of swap.
                unsafe {
                    merge(&mut v[0..(i + 8)], i, swap_ptr, is_less);
                }
                i += 8;
                merge_count -= 1;
            }

            insertion_sort_shift_left(v, i, is_less);

            return true;
        }
    } else {
        const MAX_NO_ALLOC_SIZE: usize = 20;
        if len <= MAX_NO_ALLOC_SIZE {
            insertion_sort_shift_right(v, start, is_less);
            return true;
        }
    }

    false
}

/// Takes a range as denoted by start and end, that is already sorted and extends it if necessary
/// with sorts optimized for smaller ranges such as insertion sort.
#[cfg(not(no_global_oom_handling))]
fn provide_sorted_batch<T, F>(v: &mut [T], mut start: usize, end: usize, is_less: &mut F) -> usize
where
    F: FnMut(&T, &T) -> bool,
{
    debug_assert!(end > start);

    // This value is a balance between least comparisons and best performance, as
    // influenced by for example cache locality.
    const MIN_INSERTION_RUN: usize = 10;

    // Insert some more elements into the run if it's too short. Insertion sort is faster than
    // merge sort on short sequences, so this significantly improves performance.
    let start_found = start;
    let start_end_diff = end - start;

    const FAST_SORT_SIZE: usize = 24;

    if qualifies_for_branchless_sort::<T>() && end >= (FAST_SORT_SIZE + 3) && start_end_diff <= 6 {
        // For random inputs on average how many elements are naturally already sorted
        // (start_end_diff) will be relatively small. And it's faster to avoid a merge operation
        // between the newly sorted elements on the left by the sort network and the already sorted
        // elements. Instead if there are 3 or fewer already sorted elements they get merged by
        // participating in the sort network. This wastes the information that they are already
        // sorted, but extra branching is not worth it.
        //
        // Note, this optimization significantly reduces comparison count, versus just always using
        // insertion_sort_shift_left. Insertion sort is faster than calling merge here, and this is
        // yet faster starting at FAST_SORT_SIZE 20.
        let is_small_pre_sorted = start_end_diff <= 3;

        start = if is_small_pre_sorted {
            end - FAST_SORT_SIZE
        } else {
            start_found - (FAST_SORT_SIZE - 3)
        };

        // SAFETY: start >= 0 && start + FAST_SORT_SIZE <= end
        unsafe {
            // Use a straight-line sorting network here instead of some hybrid network with early
            // exit. If the input is already sorted the previous adaptive analysis path of TimSort
            // ought to have found it. So we prefer minimizing the total amount of comparisons,
            // which are user provided and may be of arbitrary cost.
            sort24_stable(&mut v[start..(start + FAST_SORT_SIZE)], is_less);
        }

        // For most patterns this branch should have good prediction accuracy.
        if !is_small_pre_sorted {
            insertion_sort_shift_left(&mut v[start..end], FAST_SORT_SIZE, is_less);
        }
    } else if start_end_diff < MIN_INSERTION_RUN && start != 0 {
        // v[start_found..end] are elements that are already sorted in the input. We want to extend
        // the sorted region to the left, so we push up MIN_INSERTION_RUN - 1 to the right. Which is
        // more efficient that trying to push those already sorted elements to the left.

        start = if end >= MIN_INSERTION_RUN {
            end - MIN_INSERTION_RUN
        } else {
            0
        };

        insertion_sort_shift_right(&mut v[start..end], start_found - start, is_less);
    }

    start
}

// When dropped, copies from `src` into `dest`.
struct InsertionHole<T> {
    src: *const T,
    dest: *mut T,
}

impl<T> Drop for InsertionHole<T> {
    fn drop(&mut self) {
        unsafe {
            ptr::copy_nonoverlapping(self.src, self.dest, 1);
        }
    }
}

/// Inserts `v[v.len() - 1]` into pre-sorted sequence `v[..v.len() - 1]` so that whole `v[..]`
/// becomes sorted.
unsafe fn insert_tail<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    debug_assert!(v.len() >= 2);

    let arr_ptr = v.as_mut_ptr();
    let i = v.len() - 1;

    // SAFETY: caller must ensure v is at least len 2.
    unsafe {
        // See insert_head which talks about why this approach is beneficial.
        let i_ptr = arr_ptr.add(i);

        // It's important that we use i_ptr here. If this check is positive and we continue,
        // We want to make sure that no other copy of the value was seen by is_less.
        // Otherwise we would have to copy it back.
        if !is_less(&*i_ptr, &*i_ptr.sub(1)) {
            return;
        }

        // It's important, that we use tmp for comparison from now on. As it is the value that
        // will be copied back. And notionally we could have created a divergence if we copy
        // back the wrong value.
        let tmp = mem::ManuallyDrop::new(ptr::read(i_ptr));
        // Intermediate state of the insertion process is always tracked by `hole`, which
        // serves two purposes:
        // 1. Protects integrity of `v` from panics in `is_less`.
        // 2. Fills the remaining hole in `v` in the end.
        //
        // Panic safety:
        //
        // If `is_less` panics at any point during the process, `hole` will get dropped and
        // fill the hole in `v` with `tmp`, thus ensuring that `v` still holds every object it
        // initially held exactly once.
        let mut hole = InsertionHole {
            src: &*tmp,
            dest: i_ptr.sub(1),
        };
        ptr::copy_nonoverlapping(hole.dest, i_ptr, 1);

        // SAFETY: We know i is at least 1.
        for j in (0..(i - 1)).rev() {
            let j_ptr = arr_ptr.add(j);
            if !is_less(&*tmp, &*j_ptr) {
                break;
            }

            ptr::copy_nonoverlapping(j_ptr, hole.dest, 1);
            hole.dest = j_ptr;
        }
        // `hole` gets dropped and thus copies `tmp` into the remaining hole in `v`.
    }
}

/// Sort `v` assuming `v[..offset]` is already sorted.
///
/// Never inline this function to avoid code bloat. It still optimizes nicely and has practically no
/// performance impact. Even improving performance in some cases.
#[inline(never)]
fn insertion_sort_shift_left<T, F>(v: &mut [T], offset: usize, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    let len = v.len();

    // This is a logic but not a safety bug.
    debug_assert!(offset != 0 && offset <= len);

    if ((len < 2) as u8 + (offset == 0) as u8) != 0 {
        return;
    }

    // Shift each element of the unsorted region v[i..] as far left as is needed to make v sorted.
    for i in offset..len {
        // SAFETY: we tested that len >= 2.
        unsafe {
            // Maybe use insert_head here and avoid additional code.
            insert_tail(&mut v[..=i], is_less);
        }
    }
}

/// Sort `v` assuming `v[offset..]` is already sorted.
///
/// Never inline this function to avoid code bloat. It still optimizes nicely and has practically no
/// performance impact. Even improving performance in some cases.
#[inline(never)]
fn insertion_sort_shift_right<T, F>(v: &mut [T], offset: usize, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    let len = v.len();

    // This is a logic but not a safety bug.
    debug_assert!(offset != 0 && offset <= len);

    if ((len < 2) as u8 + (offset == 0) as u8) != 0 {
        return;
    }

    // Shift each element of the unsorted region v[..i] as far left as is needed to make v sorted.
    for i in (0..offset).rev() {
        // We ensured that the slice length is always at least 2 long.
        // We know that start_found will be at least one less than end,
        // and the range is exclusive. Which gives us i always <= (end - 2).
        unsafe {
            insert_head(&mut v[i..len], is_less);
        }
    }
}

/// Inserts `v[0]` into pre-sorted sequence `v[1..]` so that whole `v[..]` becomes sorted.
///
/// This is the integral subroutine of insertion sort.
unsafe fn insert_head<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    debug_assert!(v.len() >= 2);

    if is_less(&v[1], &v[0]) {
        // SAFETY: caller must ensure v is at least len 2.
        unsafe {
            // There are three ways to implement insertion here:
            //
            // 1. Swap adjacent elements until the first one gets to its final destination.
            //    However, this way we copy data around more than is necessary. If elements are big
            //    structures (costly to copy), this method will be slow.
            //
            // 2. Iterate until the right place for the first element is found. Then shift the
            //    elements succeeding it to make room for it and finally place it into the
            //    remaining hole. This is a good method.
            //
            // 3. Copy the first element into a temporary variable. Iterate until the right place
            //    for it is found. As we go along, copy every traversed element into the slot
            //    preceding it. Finally, copy data from the temporary variable into the remaining
            //    hole. This method is very good. Benchmarks demonstrated slightly better
            //    performance than with the 2nd method.
            //
            // All methods were benchmarked, and the 3rd showed best results. So we chose that one.
            let tmp = mem::ManuallyDrop::new(ptr::read(&v[0]));

            // Intermediate state of the insertion process is always tracked by `hole`, which
            // serves two purposes:
            // 1. Protects integrity of `v` from panics in `is_less`.
            // 2. Fills the remaining hole in `v` in the end.
            //
            // Panic safety:
            //
            // If `is_less` panics at any point during the process, `hole` will get dropped and
            // fill the hole in `v` with `tmp`, thus ensuring that `v` still holds every object it
            // initially held exactly once.
            let mut hole = InsertionHole {
                src: &*tmp,
                dest: &mut v[1],
            };
            ptr::copy_nonoverlapping(&v[1], &mut v[0], 1);

            for i in 2..v.len() {
                if !is_less(&v[i], &*tmp) {
                    break;
                }
                ptr::copy_nonoverlapping(&v[i], &mut v[i - 1], 1);
                hole.dest = &mut v[i];
            }
            // `hole` gets dropped and thus copies `tmp` into the remaining hole in `v`.
        }
    }
}

/// Merges non-decreasing runs `v[..mid]` and `v[mid..]` using `buf` as temporary storage, and
/// stores the result into `v[..]`.
///
/// # Safety
///
/// The two slices must be non-empty and `mid` must be in bounds. Buffer `buf` must be long enough
/// to hold a copy of the shorter slice. Also, `T` must not be a zero-sized type.
///
/// Never inline this function to avoid code bloat. It still optimizes nicely and has practically no
/// performance impact.
#[inline(never)]
#[cfg(not(no_global_oom_handling))]
unsafe fn merge<T, F>(v: &mut [T], mid: usize, buf: *mut T, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    let len = v.len();
    let arr_ptr = v.as_mut_ptr();
    let (v_mid, v_end) = unsafe { (arr_ptr.add(mid), arr_ptr.add(len)) };

    // The merge process first copies the shorter run into `buf`. Then it traces the newly copied
    // run and the longer run forwards (or backwards), comparing their next unconsumed elements and
    // copying the lesser (or greater) one into `v`.
    //
    // As soon as the shorter run is fully consumed, the process is done. If the longer run gets
    // consumed first, then we must copy whatever is left of the shorter run into the remaining
    // hole in `v`.
    //
    // Intermediate state of the process is always tracked by `hole`, which serves two purposes:
    // 1. Protects integrity of `v` from panics in `is_less`.
    // 2. Fills the remaining hole in `v` if the longer run gets consumed first.
    //
    // Panic safety:
    //
    // If `is_less` panics at any point during the process, `hole` will get dropped and fill the
    // hole in `v` with the unconsumed range in `buf`, thus ensuring that `v` still holds every
    // object it initially held exactly once.
    let mut hole;

    if mid <= len - mid {
        // The left run is shorter.
        unsafe {
            ptr::copy_nonoverlapping(arr_ptr, buf, mid);
            hole = MergeHole {
                start: buf,
                end: buf.add(mid),
                dest: arr_ptr,
            };
        }

        // Initially, these pointers point to the beginnings of their arrays.
        let left = &mut hole.start;
        let mut right = v_mid;
        let out = &mut hole.dest;

        while *left < hole.end && right < v_end {
            // Consume the lesser side.
            // If equal, prefer the left run to maintain stability.
            unsafe {
                let to_copy = if is_less(&*right, &**left) {
                    get_and_increment(&mut right)
                } else {
                    get_and_increment(left)
                };
                ptr::copy_nonoverlapping(to_copy, get_and_increment(out), 1);
            }
        }
    } else {
        // The right run is shorter.
        unsafe {
            ptr::copy_nonoverlapping(v_mid, buf, len - mid);
            hole = MergeHole {
                start: buf,
                end: buf.add(len - mid),
                dest: v_mid,
            };
        }

        // Initially, these pointers point past the ends of their arrays.
        let left = &mut hole.dest;
        let right = &mut hole.end;
        let mut out = v_end;

        while arr_ptr < *left && buf < *right {
            // Consume the greater side.
            // If equal, prefer the right run to maintain stability.
            unsafe {
                let to_copy = if is_less(&*right.offset(-1), &*left.offset(-1)) {
                    decrement_and_get(left)
                } else {
                    decrement_and_get(right)
                };
                ptr::copy_nonoverlapping(to_copy, decrement_and_get(&mut out), 1);
            }
        }
    }
    // Finally, `hole` gets dropped. If the shorter run was not fully consumed, whatever remains of
    // it will now be copied into the hole in `v`.

    unsafe fn get_and_increment<T>(ptr: &mut *mut T) -> *mut T {
        let old = *ptr;
        *ptr = unsafe { ptr.offset(1) };
        old
    }

    unsafe fn decrement_and_get<T>(ptr: &mut *mut T) -> *mut T {
        *ptr = unsafe { ptr.offset(-1) };
        *ptr
    }

    // When dropped, copies the range `start..end` into `dest..`.
    struct MergeHole<T> {
        start: *mut T,
        end: *mut T,
        dest: *mut T,
    }

    impl<T> Drop for MergeHole<T> {
        fn drop(&mut self) {
            // `T` is not a zero-sized type, and these are pointers into a slice's elements.
            unsafe {
                let len = self.end.sub_ptr(self.start);
                ptr::copy_nonoverlapping(self.start, self.dest, len);
            }
        }
    }
}

// #[rustc_unsafe_specialization_marker]
trait IsCopyMarker {}

impl<T: Copy> IsCopyMarker for T {}

trait IsCopy {
    fn is_copy() -> bool;
}

impl<T> IsCopy for T {
    default fn is_copy() -> bool {
        false
    }
}

impl<T: IsCopyMarker> IsCopy for T {
    fn is_copy() -> bool {
        true
    }
}

#[inline]
fn qualifies_for_branchless_sort<T>() -> bool {
    // This is a heuristic, and as such it will guess wrong from time to time. The two parts broken
    // down:
    //
    // - Copy: We guess that copy types have relatively cheap comparison functions. The branchless
    //         sort does on average 8% more comparisons for random inputs and up to 50% in some
    //         circumstances. The time won avoiding branches can be offset by this increase in
    //         comparisons if the type is expensive to compare.
    //
    // - Type size: Large types are more expensive to move and the time won avoiding branches can be
    //              offset by the increased cost of moving the values.
    T::is_copy() && (mem::size_of::<T>() <= mem::size_of::<[usize; 4]>())
}

// --- Branchless sorting (less branches not zero) ---

/// Swap two values in array pointed to by a_ptr and b_ptr if b is less than a.
#[inline]
unsafe fn branchless_swap<T>(a_ptr: *mut T, b_ptr: *mut T, should_swap: bool) {
    // This is a branchless version of swap if.
    // The equivalent code with a branch would be:
    //
    // if should_swap {
    //     ptr::swap_nonoverlapping(a_ptr, b_ptr, 1);
    // }

    // Give ourselves some scratch space to work with.
    // We do not have to worry about drops: `MaybeUninit` does nothing when dropped.
    let mut tmp = mem::MaybeUninit::<T>::uninit();

    // The goal is to generate cmov instructions here.
    let a_swap_ptr = if should_swap { b_ptr } else { a_ptr };
    let b_swap_ptr = if should_swap { a_ptr } else { b_ptr };

    // SAFETY: the caller must guarantee that `a_ptr` and `b_ptr` are valid for writes
    // and properly aligned, and part of the same allocation, and do not alias.
    unsafe {
        ptr::copy_nonoverlapping(b_swap_ptr, tmp.as_mut_ptr(), 1);
        ptr::copy(a_swap_ptr, a_ptr, 1);
        ptr::copy_nonoverlapping(tmp.as_ptr(), b_ptr, 1);
    }
}

/// Swap two values in array pointed to by a_ptr and b_ptr if b is less than a.
#[inline]
unsafe fn swap_if_less<T, F>(arr_ptr: *mut T, a: usize, b: usize, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: the caller must guarantee that `a` and `b` each added to `arr_ptr` yield valid
    // pointers into `arr_ptr`. and properly aligned, and part of the same allocation, and do not
    // alias. `a` and `b` must be different numbers.
    unsafe {
        debug_assert!(a != b);

        let a_ptr = arr_ptr.add(a);
        let b_ptr = arr_ptr.add(b);

        // PANIC SAFETY: if is_less panics, no scratch memory was created and the slice should still be
        // in a well defined state, without duplicates.

        // Important to only swap if it is more and not if it is equal. is_less should return false for
        // equal, so we don't swap.
        let should_swap = is_less(&*b_ptr, &*a_ptr);

        branchless_swap(a_ptr, b_ptr, should_swap);
    }
}

/// Comparing and swapping anything but adjacent elements will yield a non stable sort.
/// So this must be fundamental building block for stable sorting networks.
#[inline]
unsafe fn swap_next_if_less<T, F>(arr_ptr: *mut T, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: the caller must guarantee that `arr_ptr` and `arr_ptr.add(1)` yield valid
    // pointers that are properly aligned, and part of the same allocation.
    unsafe {
        swap_if_less(arr_ptr, 0, 1, is_less);
    }
}

/// Sort 8 elements
///
/// Never inline this function to avoid code bloat. It still optimizes nicely and has practically no
/// performance impact.
#[inline(never)]
unsafe fn sort8_stable<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: caller must ensure v is at least len 8.
    unsafe {
        debug_assert!(v.len() == 8);

        let arr_ptr = v.as_mut_ptr();

        // Transposition sorting-network, by only comparing and swapping adjacent wires we have a stable
        // sorting-network. Sorting-networks are great at leveraging Instruction-Level-Parallelism
        // (ILP), they expose multiple comparisons in straight-line code with builtin data-dependency
        // parallelism and ordering per layer. This has to do 28 comparisons in contrast to the 19
        // comparisons done by an optimal size 8 unstable sorting-network.
        swap_next_if_less(arr_ptr.add(0), is_less);
        swap_next_if_less(arr_ptr.add(2), is_less);
        swap_next_if_less(arr_ptr.add(4), is_less);
        swap_next_if_less(arr_ptr.add(6), is_less);

        swap_next_if_less(arr_ptr.add(1), is_less);
        swap_next_if_less(arr_ptr.add(3), is_less);
        swap_next_if_less(arr_ptr.add(5), is_less);

        swap_next_if_less(arr_ptr.add(0), is_less);
        swap_next_if_less(arr_ptr.add(2), is_less);
        swap_next_if_less(arr_ptr.add(4), is_less);
        swap_next_if_less(arr_ptr.add(6), is_less);

        swap_next_if_less(arr_ptr.add(1), is_less);
        swap_next_if_less(arr_ptr.add(3), is_less);
        swap_next_if_less(arr_ptr.add(5), is_less);

        swap_next_if_less(arr_ptr.add(0), is_less);
        swap_next_if_less(arr_ptr.add(2), is_less);
        swap_next_if_less(arr_ptr.add(4), is_less);
        swap_next_if_less(arr_ptr.add(6), is_less);

        swap_next_if_less(arr_ptr.add(1), is_less);
        swap_next_if_less(arr_ptr.add(3), is_less);
        swap_next_if_less(arr_ptr.add(5), is_less);

        swap_next_if_less(arr_ptr.add(0), is_less);
        swap_next_if_less(arr_ptr.add(2), is_less);
        swap_next_if_less(arr_ptr.add(4), is_less);
        swap_next_if_less(arr_ptr.add(6), is_less);

        swap_next_if_less(arr_ptr.add(1), is_less);
        swap_next_if_less(arr_ptr.add(3), is_less);
        swap_next_if_less(arr_ptr.add(5), is_less);
    }
}

unsafe fn sort24_stable<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: caller must ensure v is exactly len 24.
    unsafe {
        debug_assert!(v.len() == 24);

        sort8_stable(&mut v[0..8], is_less);
        sort8_stable(&mut v[8..16], is_less);
        sort8_stable(&mut v[16..24], is_less);

        // We only need place for 8 entries because we know both sides are of length 8.
        let mut swap = mem::MaybeUninit::<[T; 8]>::uninit();
        let swap_ptr = swap.as_mut_ptr() as *mut T;

        // We only need place for 8 entries because we know both sides are of length 8.
        merge(&mut v[..16], 8, swap_ptr, is_less);

        // We only need place for 8 entries because the shorter side is length 8.
        merge(&mut v[..24], 16, swap_ptr, is_less);
    }
}