use std::cmp::Ordering;

sort_impl!("rust_pivot_research_2_unstable");

pub fn sort<T: Ord>(data: &mut [T]) {
    pivot_research_2::sort(data);
}

pub fn sort_by<T, F: FnMut(&T, &T) -> Ordering>(data: &mut [T], compare: F) {
    pivot_research_2::sort_by(data, compare);
}
