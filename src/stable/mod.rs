pub mod rust_std;

#[cfg(feature = "max_mergesort")]
pub mod rust_max_mergesort;

#[cfg(feature = "rust_std_vendored")]
pub mod rust_std_vendored;

#[cfg(feature = "rust_wpwoodjr")]
pub mod rust_wpwoodjr;

#[cfg(feature = "rust_glidesort")]
pub mod rust_glidesort;

#[cfg(feature = "rust_driftsort")]
pub mod rust_driftsort;

#[cfg(feature = "rust_tinysort")]
pub mod rust_tinysort;

#[cfg(feature = "rust_grailsort")]
pub mod rust_grailsort;

// Call stdlib std::sort_stable sort via FFI.
#[cfg(feature = "cpp_std_sys")]
pub mod cpp_std_sys;

// Call stdlib std::sort_stable sort via FFI.
#[cfg(feature = "cpp_std_libcxx")]
pub mod cpp_std_libcxx;

// Call stdlib std::sort_stable sort via FFI.
#[cfg(feature = "cpp_std_gcc4_3")]
pub mod cpp_std_gcc4_3;

// Call powersort sort via FFI.
#[cfg(feature = "cpp_powersort")]
pub mod cpp_powersort;

// Call timsort sort via FFI.
#[cfg(feature = "cpp_timsort")]
pub mod cpp_timsort_og;

// Call timsort sort via FFI.
#[cfg(feature = "cpp_timsort")]
pub mod cpp_timsort_cross;

// Call powersort_4way sort via FFI.
#[cfg(feature = "cpp_powersort")]
pub mod cpp_powersort_4way;

// Call wikisort via FFI.
#[cfg(feature = "cpp_wikisort")]
pub mod cpp_wikisort;

// Call fluxsort sort via FFI.
// Note, this sort is only stable if the the supplied comparison returns less, equal and more.
#[cfg(feature = "c_fluxsort")]
pub mod c_fluxsort;

// Call quadsort sort via FFI.
// Note, this sort is only stable if the the supplied comparison returns less, equal and more.
#[cfg(feature = "c_quadsort")]
pub mod c_quadsort;

// Call golang slices.SortStable
#[cfg(feature = "golang_std")]
pub mod golang_std;

// timsort with timsort merge policy (original)
#[cfg(feature = "merge_policy_research")]
pub mod rust_merge_policy_research_1;

// timsort with basic shivers merge policy
#[cfg(feature = "merge_policy_research")]
pub mod rust_merge_policy_research_2;

// timsort with powersort merge policy
#[cfg(feature = "merge_policy_research")]
pub mod rust_merge_policy_research_3;

// timsort with 4-way powersort merge policy
#[cfg(feature = "merge_policy_research")]
pub mod rust_merge_policy_research_4;

// timsort with 2-merge merge policy
#[cfg(feature = "merge_policy_research")]
pub mod rust_merge_policy_research_5;

// timsort with basic branchless merge routine (original)
#[cfg(feature = "merge_routine_research")]
pub mod rust_merge_routine_research_1;

// timsort with bidirectional branchless merge routine (from glidesort?)
#[cfg(feature = "merge_routine_research")]
pub mod rust_merge_routine_research_2;

// timsort with cross merge routine (from quadsort)
#[cfg(feature = "merge_routine_research")]
pub mod rust_merge_routine_research_3;

// timsort with galloping merge routine
#[cfg(feature = "merge_routine_research")]
pub mod rust_merge_routine_research_4;

#[cfg(feature = "stable_smallsort_research")]
pub mod rust_stable_smallsort_research_1;

#[cfg(feature = "stable_smallsort_research")]
pub mod rust_stable_smallsort_research_2;

#[cfg(feature = "stable_smallsort_research")]
pub mod rust_stable_smallsort_research_3;
