pub mod rust_ipnsort;

pub mod rust_std;

// hoare with cyclic permut
#[cfg(feature = "partition_research")]
pub mod rust_partition_research_1;

// hoare with block branchless and cyclic permut
#[cfg(feature = "partition_research")]
pub mod rust_partition_research_2;

// basic lomuto
#[cfg(feature = "partition_research")]
pub mod rust_partition_research_3;

// branchless lomuto with cyclic permut
#[cfg(feature = "partition_research")]
pub mod rust_partition_research_4;

// block-based branchless lomuto
#[cfg(feature = "partition_research")]
pub mod rust_partition_research_5;

// stable partition
#[cfg(feature = "partition_research")]
pub mod rust_partition_research_6;

// median of 3
#[cfg(feature = "pivot_research")]
pub mod rust_pivot_research_1;

// adaptive compact ninther
#[cfg(feature = "pivot_research")]
pub mod rust_pivot_research_2;

// adaptive full ninther
#[cfg(feature = "pivot_research")]
pub mod rust_pivot_research_3;

// adaptive recursive ninther
#[cfg(feature = "pivot_research")]
pub mod rust_pivot_research_4;

// insertion sort
#[cfg(feature = "unstable_smallsort_research")]
pub mod rust_unstable_smallsort_research_1;

// sorting network
#[cfg(feature = "unstable_smallsort_research")]
pub mod rust_unstable_smallsort_research_2;

// block sort
#[cfg(feature = "unstable_smallsort_research")]
pub mod rust_unstable_smallsort_research_3;

#[cfg(feature = "rust_std_vendored")]
pub mod rust_std_vendored;

#[cfg(feature = "rust_dmsort")]
pub mod rust_dmsort;

#[cfg(feature = "rust_crumsort_rs")]
pub mod rust_crumsort_rs;

#[cfg(feature = "rust_tinysort")]
pub mod rust_tinysort;

#[cfg(feature = "rust_introsort")]
pub mod rust_introsort;

// Call pdqsort sort via FFI.
#[cfg(feature = "cpp_pdqsort")]
pub mod cpp_pdqsort;

// Call ips4o sort via FFI.
#[cfg(feature = "cpp_ips4o")]
pub mod cpp_ips4o;

// Call blockquicksort sort via FFI.
#[cfg(feature = "cpp_blockquicksort")]
pub mod cpp_blockquicksort;

// Call gerbens quicksort sort via FFI.
#[cfg(feature = "cpp_gerbens_qsort")]
pub mod cpp_gerbens_qsort;

// Call nanosort via FFI.
#[cfg(feature = "cpp_nanosort")]
pub mod cpp_nanosort;

// Call qsort sort via FFI.
#[cfg(feature = "c_std_sys")]
pub mod c_std_sys;

// Call crumsort sort via FFI.
#[cfg(feature = "c_crumsort")]
pub mod c_crumsort;

// Call stdlib std::sort sort via FFI.
#[cfg(feature = "cpp_std_sys")]
pub mod cpp_std_sys;

// Call stdlib std::sort sort via FFI.
#[cfg(feature = "cpp_std_libcxx")]
pub mod cpp_std_libcxx;

// Call stdlib std::sort sort via FFI.
#[cfg(feature = "cpp_std_gcc4_3")]
pub mod cpp_std_gcc4_3;

// Call golang slices.Sort
#[cfg(feature = "golang_std")]
pub mod golang_std;

// Call max quicksort
#[cfg(feature = "max_quicksort")]
pub mod rust_max_quicksort;

// Call max quicksort
#[cfg(feature = "max_synergistic_sort")]
pub mod rust_max_unstable_synergistic_sort;
