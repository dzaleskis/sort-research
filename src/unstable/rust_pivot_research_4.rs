use std::cmp::Ordering;

sort_impl!("pivot_recursive_median_3");

pub fn sort<T: Ord>(data: &mut [T]) {
    pivot_research_4::sort(data);
}

pub fn sort_by<T, F: FnMut(&T, &T) -> Ordering>(data: &mut [T], compare: F) {
    pivot_research_4::sort_by(data, compare);
}
