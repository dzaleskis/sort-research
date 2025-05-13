use sort_test_tools::instantiate_sort_tests;

type TestSort = sort_research_rs::unstable::rust_max_unstable_synergistic_sort::SortImpl;

instantiate_sort_tests!(TestSort);
