use sort_test_tools::instantiate_sort_tests;

type TestSort = sort_research_rs::stable::rust_merge_routine_research_4::SortImpl;

instantiate_sort_tests!(TestSort);
