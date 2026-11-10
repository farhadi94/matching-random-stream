# Verification status

The renamed library was rebuilt from source: **308 modules plus the root**,
with no prior project objects reused. The complete audit checks **6,504
project declarations**, including generated declarations. The final raw
dependency audit reaches only `propext`, `Classical.choice`, and `Quot.sound`.
There are **1,381 axiom-free roots** in its documented conservative graph;
this count does not assert logically minimal assumptions.

An independent migration review compared all **6,504 elaborated statement
types** and **1,566 non-proof computational definitions** with the reviewed
pre-rename library, under explicit name mappings. All comparisons pass.
The real resume check also passes and verifies source, compiler, external
proof-artifact, and direct dependency-output identities before reuse.

The immutable build-time manifest is preserved in
`evidence/build-source-manifest.json`. Its pending-status prose records the
snapshot before verification; completed results are recorded in
`evidence/verification.json`. The release manifest includes subsequent
documentation changes and a strengthened auditor. All proof modules, root,
compiler/verifier configuration and certificate/checker bytes are unchanged.
The published auditor is byte-identical to the independently reviewed
candidate successfully executed against the freshly built objects.

Lean's exported cached summaries gave 1,385 axiom-free declarations before
renaming and 1,383 afterward, with eleven per-declaration set differences.
The original driver's failed expectation of the old count is preserved in
the verification provenance. The final auditor traverses raw dependencies,
including cycles, and agrees on every root with an independent graph check.
No matching theorem or approximation coefficient changed.

The precise formal scope and implementation boundary are described in
README.md and THEOREM_MAP.md.
