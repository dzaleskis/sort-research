use std::cmp::Ordering;

sort_impl!("partition_hoare_branchy_cyclic");

pub fn sort<T: Ord>(data: &mut [T]) {
    partition_research_2::sort(data);
}

pub fn sort_by<T, F: FnMut(&T, &T) -> Ordering>(data: &mut [T], compare: F) {
    partition_research_2::sort_by(data, compare);
}
