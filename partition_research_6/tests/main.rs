use sort_test_tools::{instantiate_sort_tests, Sort};

struct SortImpl {}

impl Sort for SortImpl {
    fn name() -> String {
        "partition_lomuto_branchless_block".into()
    }

    fn sort<T>(arr: &mut [T])
    where
        T: Ord,
    {
        partition_research_6::sort(arr);
    }

    fn sort_by<T, F>(arr: &mut [T], compare: F)
    where
        F: FnMut(&T, &T) -> std::cmp::Ordering,
    {
        partition_research_6::sort_by(arr, compare);
    }
}

instantiate_sort_tests!(SortImpl);
