use sort_test_tools::{instantiate_sort_tests, Sort};

struct SortImpl {}

impl Sort for SortImpl {
    fn name() -> String {
        "rust_pivot_research_5_unstable".into()
    }

    fn sort<T>(arr: &mut [T])
    where
        T: Ord,
    {
        pivot_research_5::sort(arr);
    }

    fn sort_by<T, F>(arr: &mut [T], compare: F)
    where
        F: FnMut(&T, &T) -> std::cmp::Ordering,
    {
        pivot_research_5::sort_by(arr, compare);
    }
}

instantiate_sort_tests!(SortImpl);
