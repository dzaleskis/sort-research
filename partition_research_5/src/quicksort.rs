use core::cmp;
use core::intrinsics;
use core::mem::{self, ManuallyDrop};
use core::ptr;

use crate::heapsort;
use crate::smallsort::UnstableSmallSortTypeImpl;

/// Sorts `v` recursively.
///
/// If the slice had a predecessor in the original array, it is specified as `ancestor_pivot`.
///
/// `limit` is the number of allowed imbalanced partitions before switching to `heapsort`. If zero,
/// this function will immediately switch to heapsort.
pub(crate) fn quicksort<'a, T, F>(
    mut v: &'a mut [T],
    mut ancestor_pivot: Option<&'a T>,
    mut limit: u32,
    is_less: &mut F,
) where
    F: FnMut(&T, &T) -> bool,
{
    loop {
        // println!("len: {}", v.len());

        if v.len() <= T::small_sort_threshold() {
            T::small_sort(v, is_less);
            return;
        }

        // If too many bad pivot choices were made, simply fall back to heapsort in order to
        // guarantee `O(N x log(N))` worst-case.
        if limit == 0 {
            heapsort::heapsort(v, is_less);
            return;
        }

        limit -= 1;

        // Choose a pivot and try guessing whether the slice is already sorted.
        let pivot_pos = crate::pivot::choose_pivot(v, is_less);

        // If the chosen pivot is equal to the predecessor, then it's the smallest element in the
        // slice. Partition the slice into elements equal to and elements greater than the pivot.
        // This case is usually hit when the slice contains many duplicate elements.
        if let Some(p) = ancestor_pivot {
            // SAFETY: We assume choose_pivot yields an in-bounds position.
            if !is_less(p, unsafe { v.get_unchecked(pivot_pos) }) {
                let num_lt = partition(v, pivot_pos, &mut |a, b| !is_less(b, a));

                // Continue sorting elements greater than the pivot. We know that `num_lt` contains
                // the pivot. So we can continue after `num_lt`.
                v = &mut v[(num_lt + 1)..];
                ancestor_pivot = None;
                continue;
            }
        }

        // Partition the slice.
        let num_lt = partition(v, pivot_pos, is_less);
        // SAFETY: partition ensures that `num_lt` will be in-bounds.
        unsafe { intrinsics::assume(num_lt < v.len()) };

        // Split the slice into `left`, `pivot`, and `right`.
        let (left, right) = v.split_at_mut(num_lt);
        let (pivot, right) = right.split_at_mut(1);
        let pivot = &pivot[0];

        // Recurse into the left side. We have a fixed recursion limit, testing shows no real
        // benefit for recursing into the shorter side.
        quicksort(left, ancestor_pivot, limit, is_less);

        // Continue with the right side.
        v = right;
        ancestor_pivot = Some(pivot);
    }
}

// TODO move to main docs.
// Instead of swapping one pair at the time, it is more efficient to perform a cyclic
// permutation. This is not strictly equivalent to swapping, but produces a similar
// result using fewer memory operations.
//
// Example cyclic permutation to swap A,B,C,D with W,X,Y,Z
//
// A -> TMP
// Z -> A   | Z,B,C,D ___ W,X,Y,Z
//
// Loop iter 1
// B -> Z   | Z,B,C,D ___ W,X,Y,B
// Y -> B   | Z,Y,C,D ___ W,X,Y,B
//
// Loop iter 2
// C -> Y   | Z,Y,C,D ___ W,X,C,B
// X -> C   | Z,Y,X,D ___ W,X,C,B
//
// Loop iter 3
// D -> X   | Z,Y,X,D ___ W,D,C,B
// W -> D   | Z,Y,X,W ___ W,D,C,B
//
// TMP -> W | Z,Y,X,W ___ A,D,C,B

/// Takes the input slice `v` and re-arranges elements such that when the call returns normally
/// all elements that compare true for `is_less(elem, pivot)` where `pivot == v[pivot_pos]` are
/// on the left side of `v` followed by the other elements, notionally considered greater or
/// equal to `pivot`.
///
/// Returns the number of elements that are compared true for `is_less(elem, pivot)`.
///
/// If `is_less` does not implement a total order the resulting order and return value are
/// unspecified. All original elements will remain in `v` and any possible modifications via
/// interior mutability will be observable. Same is true if `is_less` panics or `v.len()`
/// exceeds `scratch.len()`.
fn partition<T, F>(v: &mut [T], pivot: usize, is_less: &mut F) -> usize
where
    F: FnMut(&T, &T) -> bool,
{
    let len = v.len();

    // Allows for panic-free code-gen by proving this property to the compiler.
    if len == 0 {
        return 0;
    }

    // Allows for panic-free code-gen by proving this property to the compiler.
    if pivot >= len {
        intrinsics::abort();
    }

    // Place the pivot at the beginning of slice.
    v.swap(0, pivot);
    let (pivot, v_without_pivot) = v.split_at_mut(1);

    // Assuming that Rust generates noalias LLVM IR we can be sure that a partition function
    // signature of the form `(v: &mut [T], pivot: &T)` guarantees that pivot and v can't alias.
    // Having this guarantee is crucial for optimizations. It's possible to copy the pivot value
    // into a stack value, but this creates issues for types with interior mutability mandating
    // a drop guard.
    let pivot = &mut pivot[0];

    // This construct is used to limit the LLVM IR generated, which saves large amounts of
    // compile-time by only instantiating the code that is needed. Idea by Frank Steffahn.
    let num_lt = partition_lomuto_branchless_cyclic(v_without_pivot, pivot, is_less);

    // Place the pivot between the two partitions.
    v.swap(0, num_lt);

    num_lt
}

fn partition_lomuto_branchless_cyclic<T, F>(v: &mut [T], pivot: &T, is_less: &mut F) -> usize
where
    F: FnMut(&T, &T) -> bool,
{
    // Novel partition implementation by Lukas Bergdoll and Orson Peters. Branchless Lomuto
    // partition paired with a cyclic permutation. TODO link writeup.

    let len = v.len();
    let v_base = v.as_mut_ptr();

    if len == 0 {
        return 0;
    }

    // SAFETY: We checked that `len` is more than zero, which means that reading `v_base` is safe to
    // do. From there we have a bounded loop where `v_base.add(i)` is guaranteed in-bounds. `v` and
    // `pivot` can't alias because of type system rules. The drop-guard `gap` ensures that should
    // `is_less` panic we always overwrite the duplicate in the input. `gap.pos` stores the previous
    // value of `right` and starts at `v_base` and so it too is in-bounds. Given `UNROLL_LEN == 2`
    // after the main loop we either have A) the last element in `v` that has not yet been processed
    // because `len % 2 != 0`, or B) all elements have been processed except the gap value that was
    // saved at the beginning with `ptr::read(v_base)`. In the case A) the loop will iterate twice,
    // first performing loop_body to take care of the last element that didn't fit into the unroll.
    // After that the behavior is the same as for B) where we use the saved value as `right` to
    // overwrite the duplicate. If this very last call to `is_less` panics the saved value will be
    // copied back including all possible changes via interior mutability. If `is_less` does not
    // panic and the code continues we overwrite the duplicate and do `right = right.add(1)`, this
    // is safe to do with `&mut *gap.value` because `T` is the same as `[T; 1]` and generating a
    // pointer one past the allocation is safe.
    unsafe {
        let mut loop_body = |state: &mut PartitionState<T>| {
            let right_is_lt = is_less(&*state.right, pivot);
            let left = v_base.add(state.num_lt);

            ptr::copy(left, state.gap.pos, 1);
            ptr::copy_nonoverlapping(state.right, left, 1);

            state.gap.pos = state.right;
            state.num_lt += right_is_lt as usize;

            state.right = state.right.add(1);
        };

        // Ideally we could just use GapGuard in PartitionState, but the reference that is
        // materialized with `&mut state` when calling `loop_body` would create a mutable reference
        // to the parent struct that contains the gap value, invalidating the reference pointer
        // created from a reference to the gap value in the cleanup loop. This is only an issue
        // under Stacked Borrows, Tree Borrows accepts the intuitive code using GapGuard as valid.
        let mut gap_value = ManuallyDrop::new(ptr::read(v_base));

        let mut state = PartitionState {
            num_lt: 0,
            right: v_base.add(1),

            gap: GapGuardRaw {
                pos: v_base,
                value: &mut *gap_value,
            },
        };

        // Manual unrolling that works well on x86, Arm and with opt-level=s without murdering
        // compile-times. Leaving this to the compiler yields ok to bad results.
        let unroll_len = if const { mem::size_of::<T>() <= 16 } {
            2
        } else {
            1
        };

        let unroll_end = v_base.add(len - (unroll_len - 1));
        while state.right < unroll_end {
            if unroll_len == 2 {
                loop_body(&mut state);
                loop_body(&mut state);
            } else {
                loop_body(&mut state);
            }
        }

        // Single instantiate `loop_body` for both the unroll cleanup and cyclic permutation
        // cleanup. Optimizes binary-size and compile-time.
        let end = v_base.add(len);
        loop {
            let is_done = state.right == end;
            state.right = if is_done {
                state.gap.value
            } else {
                state.right
            };

            loop_body(&mut state);

            if is_done {
                mem::forget(state.gap);
                break;
            }
        }

        state.num_lt
    }
}

struct GapGuard<T> {
    pos: *mut T,
    value: ManuallyDrop<T>,
}

impl<T> Drop for GapGuard<T> {
    fn drop(&mut self) {
        unsafe {
            ptr::copy_nonoverlapping(&*self.value, self.pos, 1);
        }
    }
}

/// Ideally this wouldn't be needed and we could just use the regular GapGuard.
/// See comment in [`partition_lomuto_branchless_cyclic`].
struct GapGuardRaw<T> {
    pos: *mut T,
    value: *mut T,
}

impl<T> Drop for GapGuardRaw<T> {
    fn drop(&mut self) {
        unsafe {
            ptr::copy_nonoverlapping(self.value, self.pos, 1);
        }
    }
}

struct PartitionState<T> {
    // The current element that is being looked at, scans left to right through slice.
    right: *mut T,
    // Counts the number of elements that compared less-than, also works around:
    // https://github.com/rust-lang/rust/issues/117128
    num_lt: usize,
    // Gap guard that tracks the temporary duplicate in the input.
    gap: GapGuardRaw<T>,
}