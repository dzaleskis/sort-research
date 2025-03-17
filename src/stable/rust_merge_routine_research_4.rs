#![allow(unused_unsafe)]

use std::cmp::Ordering;
use std::mem::{self, size_of};
use std::ptr;

sort_impl!("merge_routine_gallop");

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
    merge_sort(arr, |a, b| a.cmp(b));
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
pub fn sort_by<T, F>(arr: &mut [T], cmp: F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    merge_sort(arr, cmp);
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
fn merge_sort<T, F>(v: &mut [T], mut cmp: F)
where
    F: FnMut(&T, &T) -> Ordering,
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
                insert_head(&mut v[i..], &mut |a, b| cmp(a, b) == Ordering::Less);
            }
        }
        return;
    }

    // Allocate a buffer to use as scratch memory. We keep the length 0 so we can keep in it
    // shallow copies of the contents of `v` without risking the dtors running on copies if
    // `is_less` panics. When merging two sorted runs, this buffer holds a copy of the shorter run,
    // which will always have length at most `len / 2`.
    let mut buf = Vec::with_capacity(len / 2);

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
                if cmp(v.get_unchecked(start + 1), v.get_unchecked(start)) == Ordering::Less {
                    while start > 0
                        && cmp(v.get_unchecked(start), v.get_unchecked(start - 1)) == Ordering::Less
                    {
                        start -= 1;
                    }
                    v[start..end].reverse();
                } else {
                    while start > 0
                        && cmp(v.get_unchecked(start), v.get_unchecked(start - 1)) != Ordering::Less
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
            insert_head(&mut v[start..end], &mut |a, b| cmp(a, b) == Ordering::Less);
        }

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
                    buf.as_mut_ptr(),
                    &mut cmp,
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
        start: usize,
        len: usize,
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

/// Merge implementation switch.
///
/// `c(a, b)` should return std::cmp::Ordering::Greater when `a` is greater than `b`.
pub fn merge<T, F>(list: &mut [T], mut first_len: usize, buf: *mut T, cmp: &mut F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    let second_len: usize;
    let first_off: usize;
    if first_len == 0 {
        return;
    }

    unsafe {
        let (first, second) = list.split_at_mut(first_len);
        second_len = gallop_left(
            first.get_unchecked(first_len - 1),
            second,
            GallopMode::Reverse,
            cmp,
        );
        if second_len == 0 {
            return;
        }
        first_off = gallop_right(second.get_unchecked(0), first, GallopMode::Forward, cmp);
        first_len -= first_off;
        if first_len == 0 {
            return;
        }
    }
    let nlist = list
        .split_at_mut(first_off)
        .1
        .split_at_mut(first_len + second_len)
        .0;
    if first_len > second_len {
        merge_hi(nlist, first_len, second_len, cmp);
    } else {
        merge_lo(nlist, first_len, cmp);
    }
}

/// The number of times any one run can win before we try galloping.
/// Change this during testing.
const MIN_GALLOP: usize = 7;

/// Merge implementation used when the first run is smaller than the second.
pub fn merge_lo<T, F>(list: &mut [T], first_len: usize, cmp: &mut F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    unsafe {
        let mut state = MergeLo::new(list, first_len);
        state.merge(cmp);
    }
}

/// Implementation of `merge_lo`. We need to have an object in order to
/// implement panic safety.
struct MergeLo<'a, T: 'a> {
    list_len: usize,
    first_pos: usize,
    first_len: usize,
    second_pos: usize,
    dest_pos: usize,
    list: &'a mut [T],
    tmp: Vec<T>,
}
impl<'a, T: 'a> MergeLo<'a, T> {
    /// Constructor for a lower merge.
    unsafe fn new(list: &'a mut [T], first_len: usize) -> Self {
        let mut ret_val = MergeLo {
            list_len: list.len(),
            first_pos: 0,
            first_len: first_len,
            second_pos: first_len,
            dest_pos: 0,
            list: list,
            tmp: Vec::with_capacity(first_len),
        };
        // First, move the smallest run into temporary storage, leaving the
        // original contents uninitialized.
        ret_val.tmp.set_len(first_len);
        for i in 0..first_len {
            ptr::copy_nonoverlapping(
                ret_val.list.get_unchecked(i),
                ret_val.tmp.get_unchecked_mut(i),
                1,
            );
        }
        ret_val
    }
    /// Perform the one-by-one comparison and insertion.
    unsafe fn merge<F>(&mut self, cmp: &mut F)
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        let mut first_count = 0;
        let mut second_count = 0;
        while self.second_pos > self.dest_pos && self.second_pos < self.list_len {
            debug_assert!(self.first_pos + (self.second_pos - self.first_len) == self.dest_pos);
            if (second_count | first_count) < MIN_GALLOP {
                // One-at-a-time mode.
                if cmp(
                    self.tmp.get_unchecked(self.first_pos),
                    self.list.get_unchecked(self.second_pos),
                ) == Ordering::Greater
                {
                    ptr::copy_nonoverlapping(
                        self.list.get_unchecked(self.second_pos),
                        self.list.get_unchecked_mut(self.dest_pos),
                        1,
                    );
                    self.second_pos += 1;
                    second_count += 1;
                    first_count = 0;
                } else {
                    ptr::copy_nonoverlapping(
                        self.tmp.get_unchecked(self.first_pos),
                        self.list.get_unchecked_mut(self.dest_pos),
                        1,
                    );
                    self.first_pos += 1;
                    first_count += 1;
                    second_count = 0;
                }
                self.dest_pos += 1;
            } else {
                // Galloping mode.
                second_count = gallop_left(
                    self.tmp.get_unchecked(self.first_pos),
                    self.list.split_at(self.second_pos).1,
                    GallopMode::Forward,
                    cmp,
                );
                ptr::copy(
                    self.list.get_unchecked(self.second_pos),
                    self.list.get_unchecked_mut(self.dest_pos),
                    second_count,
                );
                self.dest_pos += second_count;
                self.second_pos += second_count;
                debug_assert!(self.first_pos + (self.second_pos - self.first_len) == self.dest_pos);
                if self.second_pos > self.dest_pos && self.second_pos < self.list_len {
                    first_count = gallop_right(
                        self.list.get_unchecked(self.second_pos),
                        self.tmp.split_at(self.first_pos).1,
                        GallopMode::Forward,
                        cmp,
                    );
                    ptr::copy_nonoverlapping(
                        self.tmp.get_unchecked(self.first_pos),
                        self.list.get_unchecked_mut(self.dest_pos),
                        first_count,
                    );
                    self.dest_pos += first_count;
                    self.first_pos += first_count;
                }
            }
        }
    }
}
impl<'a, T: 'a> Drop for MergeLo<'a, T> {
    /// Copy all remaining items in the temporary storage into the list.
    /// If the comparator panics, the result will not be sorted, but will still
    /// contain no duplicates or uninitialized spots.
    fn drop(&mut self) {
        unsafe {
            // Make sure that the entire tmp storage is consumed. Since there are no uninitialized
            // spaces before dest_pos, and no uninitialized space after first_pos, this will ensure
            // that there are no uninitialized spaces inside the slice after we drop. Thus, the
            // function is safe.
            if self.first_pos < self.first_len {
                ptr::copy_nonoverlapping(
                    self.tmp.get_unchecked(self.first_pos),
                    self.list.get_unchecked_mut(self.dest_pos),
                    self.first_len - self.first_pos,
                );
            }
            // The temporary storage is now full of nothing but uninitialized.
            // We want to deallocate the space, but not call the destructors.
            self.tmp.set_len(0);
        }
    }
}

/// Merge implementation used when the first run is larger than the second.
pub fn merge_hi<T, F>(list: &mut [T], first_len: usize, second_len: usize, cmp: &mut F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    unsafe {
        let mut state = MergeHi::new(list, first_len, second_len);
        state.merge(cmp);
    }
}

/// Implementation of `merge_hi`. We need to have an object in order to
/// implement panic safety.
struct MergeHi<'a, T: 'a> {
    first_pos: isize,
    second_pos: isize,
    dest_pos: isize,
    list: &'a mut [T],
    tmp: Vec<T>,
}

impl<'a, T: 'a> MergeHi<'a, T> {
    /// Constructor for a higher merge.
    unsafe fn new(list: &'a mut [T], first_len: usize, second_len: usize) -> Self {
        let mut ret_val = MergeHi {
            first_pos: first_len as isize - 1,
            second_pos: second_len as isize - 1,
            dest_pos: list.len() as isize - 1,
            list: list,
            tmp: Vec::with_capacity(second_len),
        };
        // First, move the smallest run into temporary storage, leaving the
        // original contents uninitialized.
        ret_val.tmp.set_len(second_len);
        for i in 0..second_len {
            ptr::copy_nonoverlapping(
                ret_val.list.get_unchecked(i + first_len),
                ret_val.tmp.get_unchecked_mut(i),
                1,
            );
        }
        ret_val
    }
    /// Perform the one-by-one comparison and insertion.
    unsafe fn merge<F>(&mut self, cmp: &mut F)
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        let mut first_count: usize = 0;
        let mut second_count: usize = 0;
        while self.first_pos < self.dest_pos && self.first_pos >= 0 {
            debug_assert!(self.first_pos + self.second_pos + 1 == self.dest_pos);
            if (second_count | first_count) < MIN_GALLOP {
                // One-at-a-time mode.
                if cmp(
                    self.tmp.get_unchecked(self.second_pos as usize),
                    self.list.get_unchecked(self.first_pos as usize),
                ) != Ordering::Less
                {
                    ptr::copy_nonoverlapping(
                        self.tmp.get_unchecked(self.second_pos as usize),
                        self.list.get_unchecked_mut(self.dest_pos as usize),
                        1,
                    );
                    self.second_pos -= 1;
                } else {
                    ptr::copy_nonoverlapping(
                        self.list.get_unchecked(self.first_pos as usize),
                        self.list.get_unchecked_mut(self.dest_pos as usize),
                        1,
                    );
                    self.first_pos -= 1;
                }
                self.dest_pos -= 1;
            } else {
                // Galloping mode.
                first_count = self.first_pos as usize + 1
                    - gallop_right(
                        self.tmp.get_unchecked(self.second_pos as usize),
                        self.list.split_at(self.first_pos as usize + 1).0,
                        GallopMode::Reverse,
                        cmp,
                    );
                copy_backwards(
                    self.list.get_unchecked(self.first_pos as usize),
                    self.list.get_unchecked_mut(self.dest_pos as usize),
                    first_count,
                );
                self.dest_pos -= first_count as isize;
                self.first_pos -= first_count as isize;
                debug_assert!(self.first_pos + self.second_pos + 1 == self.dest_pos);
                if self.first_pos < self.dest_pos && self.first_pos >= 0 {
                    second_count = self.second_pos as usize + 1
                        - gallop_left(
                            self.list.get_unchecked(self.first_pos as usize),
                            self.tmp.split_at(self.second_pos as usize + 1).0,
                            GallopMode::Reverse,
                            cmp,
                        );
                    copy_nonoverlapping_backwards(
                        self.tmp.get_unchecked(self.second_pos as usize),
                        self.list.get_unchecked_mut(self.dest_pos as usize),
                        second_count,
                    );
                    self.dest_pos -= second_count as isize;
                    self.second_pos -= second_count as isize;
                }
            }
        }
    }
}

/// Perform a backwards `ptr::copy_nonoverlapping`. Behave identically when size = 1, but behave
/// differently all other times
unsafe fn copy_backwards<T>(src: *const T, dest: *mut T, size: usize) {
    ptr::copy(
        src.offset(-(size as isize - 1)),
        dest.offset(-(size as isize - 1)),
        size,
    )
}

/// Perform a backwards `ptr::copy_nonoverlapping`. Behave identically when size = 1, but behave
/// differently all other times
unsafe fn copy_nonoverlapping_backwards<T>(src: *const T, dest: *mut T, size: usize) {
    ptr::copy_nonoverlapping(
        src.offset(-(size as isize - 1)),
        dest.offset(-(size as isize - 1)),
        size,
    )
}

impl<'a, T: 'a> Drop for MergeHi<'a, T> {
    /// Copy all remaining items in the temporary storage into the list.
    /// If the comparator panics, the result will not be sorted, but will still
    /// contain no duplicates or uninitialized spots.
    fn drop(&mut self) {
        unsafe {
            // Make sure that the entire tmp storage is consumed. Since there are no uninitialized
            // spaces before dest_pos, and no uninitialized space after first_pos, this will ensure
            // that there are no uninitialized spaces inside the slice after we drop. Thus, the
            // function is safe.
            if self.second_pos >= 0 {
                copy_nonoverlapping_backwards(
                    self.tmp.get_unchecked(self.second_pos as usize),
                    self.list.get_unchecked_mut(self.dest_pos as usize),
                    self.second_pos as usize + 1,
                );
            }

            // The temporary storage is now full of nothing but uninitialized.
            // We want to deallocate the space, but not call the destructors.
            self.tmp.set_len(0);
        }
    }
}

#[derive(Copy, Clone)]
pub enum GallopMode {
    Forward,
    Reverse,
}

/// Returns the index where key should be inserted, assuming it should be placed
/// at the beginning of any cluster of equal items.
pub fn gallop_left<T, F>(key: &T, list: &[T], mode: GallopMode, cmp: &mut F) -> usize
where
    F: FnMut(&T, &T) -> Ordering,
{
    let (mut base, mut lim) = gallop(key, list, mode, cmp);
    while lim != 0 {
        let ix = base + (lim / 2);
        match cmp(&list[ix], key) {
            Ordering::Less => {
                base = ix + 1;
                lim -= 1;
            }
            Ordering::Greater => (),
            Ordering::Equal => {
                if ix == 0 || cmp(&list[ix - 1], key) == Ordering::Less {
                    base = ix;
                    break;
                }
            }
        };
        lim /= 2;
    }
    base
}

/// Returns the index where key should be inserted, assuming it shoul be placed
/// at the end of any cluster of equal items.
pub fn gallop_right<T, F>(key: &T, list: &[T], mode: GallopMode, cmp: &mut F) -> usize
where
    F: FnMut(&T, &T) -> Ordering,
{
    let list_len = list.len();
    let (mut base, mut lim) = gallop(key, list, mode, cmp);
    while lim != 0 {
        let ix = base + (lim / 2);
        match cmp(&list[ix], key) {
            Ordering::Less => {
                base = ix + 1;
                lim -= 1;
            }
            Ordering::Greater => (),
            Ordering::Equal => {
                base = ix + 1;
                if ix == list_len - 1 || cmp(&list[ix + 1], key) == Ordering::Greater {
                    break;
                } else {
                    lim -= 1;
                }
            }
        };
        lim /= 2;
    }
    base
}

fn gallop<T, F>(key: &T, list: &[T], mode: GallopMode, cmp: &mut F) -> (usize, usize)
where
    F: FnMut(&T, &T) -> Ordering,
{
    let list_len = list.len();
    if list_len == 0 {
        return (0, 0);
    }
    match mode {
        GallopMode::Forward => {
            let mut prev_val = 0;
            let mut next_val = 1;
            while next_val < list_len {
                match cmp(&list[next_val], key) {
                    Ordering::Less => {
                        prev_val = next_val;
                        next_val = ((next_val + 1) * 2) - 1;
                    }
                    Ordering::Greater => {
                        break;
                    }
                    Ordering::Equal => {
                        next_val += 1;
                        break;
                    }
                }
            }
            if next_val > list_len {
                next_val = list_len;
            }
            (prev_val, next_val - prev_val)
        }
        GallopMode::Reverse => {
            let mut prev_val = list_len;
            let mut next_val = ((prev_val + 1) / 2) - 1;
            loop {
                match cmp(&list[next_val], key) {
                    Ordering::Greater => {
                        prev_val = next_val + 1;
                        next_val = (next_val + 1) / 2;
                        if next_val != 0 {
                            next_val -= 1;
                        } else {
                            break;
                        }
                    }
                    Ordering::Less | Ordering::Equal => {
                        break;
                    }
                }
            }
            (next_val, prev_val - next_val)
        }
    }
}
