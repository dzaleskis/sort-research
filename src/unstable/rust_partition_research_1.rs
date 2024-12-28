use std::cmp::Ordering;

sort_impl!("rust_partition_research_1_unstable");

pub fn sort<T: Ord>(data: &mut [T]) {
    partition_research_1::sort(data);
}

pub fn sort_by<T, F: FnMut(&T, &T) -> Ordering>(data: &mut [T], compare: F) {
    partition_research_1::sort_by(data, compare);
}
