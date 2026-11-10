# Verification status: Round 8

The selected 307-module dependency closure has compiled in the research
workspace. Independent reviewers checked the complete approximation
endpoints and the actual record/metadata bounds. A combined import and
transitive axiom audit passed for 6,501 project declarations, including
1,385 with no axioms. Other declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.

This record does not claim a fresh isolated rebuild of all sources.
Round 9 performs that additional reproduction with `python3 verify.py`
and independently runs the exact certificate checker. The source manifest
pins all selected files; the theorem map describes the formal scope.

The mathematical approximation guarantees are complete. Packed machine
serialization and the standard matching solver's implementation complexity
are outside the formalization, as explained in the README and paper.
