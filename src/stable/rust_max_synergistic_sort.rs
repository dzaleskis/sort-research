use std::cmp::Ordering;

sort_impl!("rust_max_synergistic");

pub fn sort<T: Ord>(data: &mut [T]) {
    sysort::sort(data);
}

pub fn sort_by<T, F: FnMut(&T, &T) -> Ordering>(data: &mut [T], compare: F) {
    sysort::sort_by(data, compare);
}
