use std::cmp::Ordering;

sort_impl!("rust_driftsort_synergistic");

pub fn sort<T: Ord>(data: &mut [T]) {
    driftsort::sort(data);
}

pub fn sort_by<T, F: FnMut(&T, &T) -> Ordering>(data: &mut [T], compare: F) {
    driftsort::sort_by(data, compare);
}
