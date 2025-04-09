use sort_test_tools::instantiate_sort_tests;

type TestSort = sort_research_rs::unstable::rust_partition_research_1::SortImpl;

instantiate_sort_tests!(TestSort);
