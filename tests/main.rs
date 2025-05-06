use sort_test_tools::instantiate_sort_tests;

type TestSort = sort_research_rs::stable::rust_stable_smallsort_research_3::SortImpl;

instantiate_sort_tests!(TestSort);
