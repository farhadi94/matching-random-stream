# Theorem map

All names below are within `RandomOrderMatching`. The public algorithm namespace
is `Algorithms`.

| Paper result | Principal Lean statement |
|---|---|
| Bounded-integer random-order approximation | `Algorithms.bounded_integer_approximation` |
| Complete bounded-integer machine contract | `Algorithms.bounded_integer_contract` |
| Unweighted random-order approximation | `Algorithms.unweighted_approximation` |
| Arbitrary positive rational-weight approximation | `Algorithms.arbitrary_weight_approximation` |
| Actual returned matching and input containment | `Algorithms.arbitrary_weight_valid`, and the bounded machine contract's validity field |
| Actual retained-window decoder equals the probability theorem's output | `Algorithms.arbitrary_weight_stream_output_eq` |
| Literal original-label permutation/output formulation | `Streaming.finalBoundedOutput_uniform_probability` |
| Historical deletion for arbitrary disjoint vertex sets and arbitrary observation times | `HistoricalDeletion.historical_deletion_bound` |
| Chronologically ordered release budget | `Unfolding.PhaseLifting.historical_deletion_budget_verified` |
| Matching-endpoint specialization with automatic time ordering | `HistoricalDeletion.Matching.historical_every_matching` |
| Historical transfer for arbitrary selected copied matchings | `HistoricalDeletion.CopiedTransfer.historical_copied_matching_bound` |
| Actual graph-to-profile construction and certificate | `Analysis.Profile.actual_graph_profile_certificate` |
| Exact rational certificate and final constant arithmetic | `Certificates.DegreeProfile.Concrete.exact_profile_certificate`, `Certificates.DegreeProfile.Concrete.post_error_ratio` |
| Actual canonical fixed-host guarantee | `Analysis.FixedHost.canonical_uniform_suffix` |
| Integration over actual acquisition histories | `Acquisition.Probability.canonical_physical_suffix_failure_probability` |
| General deterministic weight-window reduction | `Weights.Windows.planned_arbitrary_weight` |
| Every-execution canonical stored-record bound | `Resources.canonical_machine_records` |
| Explicit polynomial record bound | `Resources.canonical_machine_records_polynomial` |
| Actual live-window dictionary storage | `Resources.canonical_window_records` |
| Actual metadata and finite field ledger | `Resources.actual_metadata_cap`, `Resources.configured_actual_field_ledger` |

The approximation ratio is exactly `71295/100000`. The bounded machine
contract quantifies over all duplicate-free input lists with integer weights
in the stated range. `Weights.Windows.Machine.Good` means the output meets the ratio against
every input matching. `Probability.Restriction.permMean` is the uniform mean over the input list's
permutations. These are concrete finite probability spaces, not supplied
probabilistic success hypotheses.

The arbitrary-weight statement compares against a fixed optimum matching
of the input, with the algorithm independent of that analytical witness.
It selects its own rational accuracy and local confidence parameters. The
operational equality exposes the actual retired-window state and EOF
decoder. Inputs with at most one vertex have an explicit empty-output branch.

All approximation results apply to general graphs. Bipartite graphs are a
special case; no separate reduction of arbitrary general graphs to bipartite
input is claimed. The structural copied-transfer theorem is the reduction
used in the proof, with its precise support and chronology hypotheses.

Storage claims above concern actual record/metadata counts and finite
component encodings. They do not assert that a complete packed machine
serializer or the standard matching solver's runtime has been verified.

The historical endpoint constructs the release order internally. It permits
empty demand sets/families and tied or zero observation times. The vertex
sets are pairwise disjoint; hosts need be increasing only through the stated
terminal time. No supplied scheduling or submodularity premise remains.
