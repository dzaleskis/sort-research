use sort_test_tools::instantiate_sort_tests;

type TestSort = sort_research_rs::stable::rust_merge_policy_research_5::SortImpl;

instantiate_sort_tests!(TestSort);
