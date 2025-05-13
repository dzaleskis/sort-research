use std::cmp::Ordering;

sort_impl!("rust_max_unstable_synergistic");

pub fn sort<T: Ord>(data: &mut [T]) {
    sysort::unstable_sort(data);
}

pub fn sort_by<T, F: FnMut(&T, &T) -> Ordering>(data: &mut [T], compare: F) {
    sysort::unstable_sort_by(data, compare);
}
