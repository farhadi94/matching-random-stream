# Theorem map

All names below are within `RobustMatching`. The public algorithm namespace
is `RandomOrderMatching`.

| Paper result | Principal Lean statement |
|---|---|
| Bounded-integer random-order approximation | `RandomOrderMatching.bounded_integer_approximation` |
| Complete bounded-integer machine contract | `RandomOrderMatching.bounded_integer_contract` |
| Unweighted random-order approximation | `RandomOrderMatching.unweighted_approximation` |
| Arbitrary positive rational-weight approximation | `RandomOrderMatching.arbitrary_weight_approximation` |
| Actual returned matching and input containment | `RandomOrderMatching.arbitrary_weight_valid`, and the bounded machine contract's validity field |
| Actual retained-window decoder equals the probability theorem's output | `RandomOrderMatching.arbitrary_weight_stream_output_eq` |
| Literal original-label permutation/output formulation | `R8StreamingWrapper.finalBoundedOutput_uniform_probability` |
| Historical weighted deletion | `R7CopyDualGeneralHistory.historical_every_matching` |
| Historical transfer for arbitrary selected copied matchings | `R7CopyDualGeneralCopies.historical_copied_matching_bound` |
| Actual graph-to-profile construction and certificate | `R7SupportFlowMap.actual_graph_profile_certificate` |
| Exact rational certificate and final constant arithmetic | `R7ReductionCertificate.Concrete.exact_profile_certificate`, `post_error_ratio` |
| Actual canonical fixed-host guarantee | `R8FixedHost.canonical_uniform_suffix` |
| Integration over actual acquisition histories | `R8AcquisitionProbability.canonical_physical_suffix_failure_probability` |
| General deterministic weight-window reduction | `R8WeightWindows.planned_arbitrary_weight` |
| Every-execution canonical stored-record bound | `R8StreamingResources.canonical_machine_records` |
| Explicit polynomial record bound | `R8StreamingResources.canonical_machine_records_polynomial` |
| Actual live-window dictionary storage | `R8StreamingResources.canonical_window_records` |
| Actual metadata and finite field ledger | `R8StreamingResources.actual_metadata_cap`, `configured_actual_field_ledger` |

The approximation ratio is exactly `71295/100000`. The bounded machine
contract quantifies over all duplicate-free input lists with integer weights
in the stated range. `Machine.Good` means the output meets the ratio against
every input matching. `permMean` is the uniform mean over the input list's
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
