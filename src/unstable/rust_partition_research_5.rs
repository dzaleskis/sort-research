use std::cmp::Ordering;

sort_impl!("partition_lomuto_branchless_cyclic");

pub fn sort<T: Ord>(data: &mut [T]) {
    partition_research_5::sort(data);
}

pub fn sort_by<T, F: FnMut(&T, &T) -> Ordering>(data: &mut [T], compare: F) {
    partition_research_5::sort_by(data, compare);
}
