use sort_test_tools::{instantiate_sort_tests, Sort};

struct SortImpl {}

impl Sort for SortImpl {
    fn name() -> String {
        "pivot_full_median_9".into()
    }

    fn sort<T>(arr: &mut [T])
    where
        T: Ord,
    {
        pivot_research_3::sort(arr);
    }

    fn sort_by<T, F>(arr: &mut [T], compare: F)
    where
        F: FnMut(&T, &T) -> std::cmp::Ordering,
    {
        pivot_research_3::sort_by(arr, compare);
    }
}

instantiate_sort_tests!(SortImpl);
