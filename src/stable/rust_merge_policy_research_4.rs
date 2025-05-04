#![allow(unused_unsafe)]

use std::cmp::Ordering;
use std::mem::{self, size_of};
use std::{ptr, u8};

sort_impl!("merge_policy_powersort_4way");

/// Sorts the slice.
///
/// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*)) worst-case.
///
/// When applicable, unstable sorting is preferred because it is generally faster than stable
/// sorting and it doesn't allocate auxiliary memory.
/// See [`sort_unstable`](slice::sort_unstable).
///
/// # Current implementation
///
/// The current algorithm is an adaptive, iterative merge sort inspired by
/// [timsort](https://en.wikipedia.org/wiki/Timsort).
/// It is designed to be very fast in cases where the slice is nearly sorted, or consists of
/// two or more sorted sequences concatenated one after another.
///
/// Also, it allocates temporary storage half the size of `self`, but for short slices a
/// non-allocating insertion sort is used instead.
///
/// # Examples
///
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
///
/// v.sort();
/// assert!(v == [-5, -3, 1, 2, 4]);
/// ```
#[inline]
pub fn sort<T>(arr: &mut [T])
where
    T: Ord,
{
    merge_sort(arr, |a, b| a.lt(b));
}

/// Sorts the slice with a comparator function.
///
/// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*)) worst-case.
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
/// floats.sort_by(|a, b| a.partial_cmp(b).unwrap());
/// assert_eq!(floats, [1.0, 2.0, 3.0, 4.0, 5.0]);
/// ```
///
/// When applicable, unstable sorting is preferred because it is generally faster than stable
/// sorting and it doesn't allocate auxiliary memory.
/// See [`sort_unstable_by`](slice::sort_unstable_by).
///
/// # Current implementation
///
/// The current algorithm is an adaptive, iterative merge sort inspired by
/// [timsort](https://en.wikipedia.org/wiki/Timsort).
/// It is designed to be very fast in cases where the slice is nearly sorted, or consists of
/// two or more sorted sequences concatenated one after another.
///
/// Also, it allocates temporary storage half the size of `self`, but for short slices a
/// non-allocating insertion sort is used instead.
///
/// # Examples
///
/// ```
/// let mut v = [5, 4, 1, 3, 2];
/// v.sort_by(|a, b| a.cmp(b));
/// assert!(v == [1, 2, 3, 4, 5]);
///
/// // reverse sorting
/// v.sort_by(|a, b| b.cmp(a));
/// assert!(v == [5, 4, 3, 2, 1]);
/// ```
#[inline]
pub fn sort_by<T, F>(arr: &mut [T], mut compare: F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    merge_sort(arr, |a, b| compare(a, b) == Ordering::Less);
}

/// This merge sort borrows some (but not all) ideas from TimSort, which is described in detail
/// [here](https://github.com/python/cpython/blob/main/Objects/listsort.txt).
///
/// The algorithm identifies strictly descending and non-descending subsequences, which are called
/// natural runs. There is a stack of pending runs yet to be merged. Each newly found run is pushed
/// onto the stack, and then some pairs of adjacent runs are merged until these two invariants are
/// satisfied:
///
/// 1. for every `i` in `1..runs.len()`: `runs[i - 1].len > runs[i].len`
/// 2. for every `i` in `2..runs.len()`: `runs[i - 2].len > runs[i - 1].len + runs[i].len`
///
/// The invariants ensure that the total running time is *O*(*n* \* log(*n*)) worst-case.
fn merge_sort<T, F>(v: &mut [T], mut is_less: F)
where
    F: FnMut(&T, &T) -> bool,
{
    // Slices of up to this length get sorted using insertion sort.
    const MAX_INSERTION: usize = 20;
    // Very short runs are extended using insertion sort to span at least this many elements.
    const MIN_RUN: usize = 10;

    // Sorting has no meaningful behavior on zero-sized types.
    if size_of::<T>() == 0 {
        return;
    }

    let len = v.len();

    // Short arrays get sorted in-place via insertion sort to avoid allocations.
    if len <= MAX_INSERTION {
        if len >= 2 {
            for i in (0..len - 1).rev() {
                insert_head(&mut v[i..], &mut is_less);
            }
        }
        return;
    }

    // Allocate a buffer to use as scratch memory. We keep the length 0 so we can keep in it
    // shallow copies of the contents of `v` without risking the dtors running on copies if
    // `is_less` panics. When merging two sorted runs, this buffer holds a copy of the shorter run,
    // which will always have length at most `len / 2`.
    let mut buf = Vec::with_capacity(len);

    // In order to identify natural runs in `v`, we traverse it backwards. That might seem like a
    // strange decision, but consider the fact that merges more often go in the opposite direction
    // (forwards). According to benchmarks, merging forwards is slightly faster than merging
    // backwards. To conclude, identifying runs by traversing backwards improves performance.
    let max_stack_height = 3 * (len.ilog2() as usize / 2) + 2;
    let mut runs: Vec<Run> = Vec::with_capacity(max_stack_height);
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

        // Insert some more elements into the run if it's too short. Insertion sort is faster than
        // merge sort on short sequences, so this significantly improves performance.
        while start > 0 && end - start < MIN_RUN {
            start -= 1;
            insert_head(&mut v[start..end], &mut is_less);
        }

        let next_run = Run {
            start,
            len: end - start,
            power: 0,
        };
        end = start;

        if runs.len() >= 1 {
            unsafe {
                let last_run = runs.last_mut().unwrap_unchecked();

                last_run.power = merge_tree_depth(
                    next_run.start,
                    last_run.start,
                    last_run.start + last_run.len,
                    len,
                );

                while runs.len() >= 2 && runs[runs.len() - 2].power > runs[runs.len() - 1].power {
                    if runs.len() >= 3 && runs[runs.len() - 2].power != runs[runs.len() - 3].power {
                        merge_2_runs(v, buf.as_mut_ptr(), &mut runs, &mut is_less);
                    } else if runs.len() >= 4
                        && runs[runs.len() - 2].power != runs[runs.len() - 4].power
                    {
                        merge_3_runs(v, buf.as_mut_ptr(), &mut runs, &mut is_less);
                    } else if runs.len() >= 4 {
                        merge_4_runs(v, buf.as_mut_ptr(), &mut runs, &mut is_less);
                    } else {
                        break;
                    }
                }
            }
        }

        runs.push(next_run);
    }

    unsafe {
        if runs.len() % 3 == 0 && runs.len() >= 3 {
            merge_3_runs(v, buf.as_mut_ptr(), &mut runs, &mut is_less);
        } else if runs.len() % 3 == 2 {
            merge_2_runs(v, buf.as_mut_ptr(), &mut runs, &mut is_less);
        }

        // Merge remaining runs
        while runs.len() >= 4 {
            merge_4_runs(v, buf.as_mut_ptr(), &mut runs, &mut is_less);
        }
    }

    // Finally, exactly one run must remain in the stack.
    debug_assert!(runs.len() == 1 && runs[0].start == 0 && runs[0].len == len);

    unsafe fn merge_2_runs<T, F>(v: &mut [T], buf: *mut T, runs: &mut Vec<Run>, is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        let mut run_1 = runs.pop().unwrap_unchecked();
        let run_2 = runs.pop().unwrap_unchecked();

        merge_2way(
            &mut v[run_1.start..run_2.start + run_2.len],
            run_1.len,
            buf,
            is_less,
        );

        run_1.len = run_1.len + run_2.len;
        runs.push(run_1);
    }

    unsafe fn merge_3_runs<T, F>(v: &mut [T], buf: *mut T, runs: &mut Vec<Run>, is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        let mut run_1 = runs.pop().unwrap_unchecked();
        let run_2 = runs.pop().unwrap_unchecked();
        let run_3 = runs.pop().unwrap_unchecked();

        merge_3way(
            &mut v[run_1.start..run_3.start + run_3.len],
            run_1.len,
            run_1.len + run_2.len,
            buf,
            is_less,
        );

        run_1.len = run_1.len + run_2.len + run_3.len;
        runs.push(run_1);
    }

    unsafe fn merge_4_runs<T, F>(v: &mut [T], buf: *mut T, runs: &mut Vec<Run>, is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        let mut run_1 = runs.pop().unwrap_unchecked();
        let run_2 = runs.pop().unwrap_unchecked();
        let run_3 = runs.pop().unwrap_unchecked();
        let run_4 = runs.pop().unwrap_unchecked();

        merge_4way(
            &mut v[run_1.start..run_4.start + run_4.len],
            run_1.len,
            run_1.len + run_2.len,
            run_1.len + run_2.len + run_3.len,
            buf,
            is_less,
        );

        run_1.len = run_1.len + run_2.len + run_3.len + run_4.len;
        runs.push(run_1);
    }

    #[inline]
    fn merge_tree_depth(left: usize, mid: usize, right: usize, len: usize) -> u8 {
        let l2 = left + mid;
        let r2 = mid + right;
        let a = (l2 << 30) / len;
        let b = (r2 << 30) / len;
        let res = ((a ^ b).leading_zeros() - 1) / 2 + 1;

        return res as u8;
    }

    #[derive(Clone, Copy)]
    struct Run {
        start: usize,
        len: usize,
        power: u8,
    }
}

/// Inserts `v[0]` into pre-sorted sequence `v[1..]` so that whole `v[..]` becomes sorted.
///
/// This is the integral subroutine of insertion sort.
fn insert_head<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    if v.len() >= 2 && is_less(&v[1], &v[0]) {
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
}

unsafe fn merge_4way<T, F>(
    v: &mut [T],
    g1: usize,
    g2: usize,
    g3: usize,
    buf: *mut T,
    is_less: &mut F,
) where
    F: FnMut(&T, &T) -> bool,
{
    // merge runs 1,2 into buf
    merge_unguarded(v.as_ptr(), g2, g1, buf, is_less);
    // merge runs 3,4 into buf
    merge_unguarded(
        v.as_ptr().add(g2),
        v.len() - g2,
        g3 - g2,
        buf.add(g2),
        is_less,
    );
    // merge runs 1, 2, 3, 4 back into v
    merge_guarded(buf, v.len(), g2, v.as_mut_ptr(), is_less);
}

unsafe fn merge_3way<T, F>(v: &mut [T], g1: usize, g2: usize, buf: *mut T, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // merge runs 1,2 into buf
    merge_unguarded(v.as_ptr(), g2, g1, buf, is_less);
    // copy run 3 into buf, so it contains all of the runs
    ptr::copy_nonoverlapping(v.as_ptr().add(g2), buf.add(g2), v.len() - g2);
    // merge runs 1,2,3 which reside in buf into v
    merge_guarded(buf, v.len(), g2, v.as_mut_ptr(), is_less);
}

unsafe fn merge_2way<T, F>(v: &mut [T], g1: usize, buf: *mut T, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    merge_unguarded(v.as_ptr(), v.len(), g1, buf, is_less);
    ptr::copy_nonoverlapping(buf, v.as_mut_ptr(), v.len());
}

unsafe fn merge_guarded<T, F>(src: *const T, len: usize, mid: usize, dest: *mut T, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    let drop_guard = CopyOnDrop { src, dest, len };

    merge_unguarded(src, len, mid, dest, is_less);
    mem::forget(drop_guard);

    struct CopyOnDrop<T> {
        src: *const T,
        dest: *mut T,
        len: usize,
    }

    impl<T> Drop for CopyOnDrop<T> {
        fn drop(&mut self) {
            // SAFETY: `src` must contain `len` initialized elements, and dst must
            // be valid to write `len` elements.
            unsafe {
                ptr::copy_nonoverlapping(self.src, self.dest, self.len);
            }
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
unsafe fn merge_unguarded<T, F>(
    src: *const T,
    len: usize,
    mid: usize,
    dest: *mut T,
    is_less: &mut F,
) where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: mid and len must be in-bounds of v.
    debug_assert!(mid > 0);
    debug_assert!(mid < len);

    // SAFETY: mid and len must be in-bounds of v.
    let (src_mid, src_end) = unsafe { (src.add(mid), src.add(len)) };

    // Initially, these pointers point to the beginnings of their arrays.
    let mut left = src;
    let mut right = src_mid;
    let mut out = dest;

    while left < src_mid && right < src_end {
        // If equal, prefer the left run to maintain stability.

        // SAFETY: left and right must be valid and part of v same for out.
        unsafe {
            let is_l = is_less(&*right, &*left);
            let to_copy = if is_l { right } else { left };
            ptr::copy_nonoverlapping(to_copy, out, 1);
            out = out.add(1);
            right = right.add(is_l as usize);
            left = left.add(!is_l as usize);
        }
    }

    if left < src_mid {
        // the left run is unconsumed
        let rem_len = src_mid.offset_from_unsigned(left);
        ptr::copy_nonoverlapping(left, out, rem_len);
    } else {
        // the right run is unconsumed
        let rem_len = src_end.offset_from_unsigned(right);
        ptr::copy_nonoverlapping(right, out, rem_len);
    }
}
