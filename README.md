# Matching in random-order streams

Lean proofs and exact certificates accompanying work by Alireza Farhadi
and Mohammadtaghi Hajiaghayi.

The mathematical approximation guarantees are proved for the actual streaming
algorithms on simple general graphs, and therefore also on bipartite graphs:

| Weights | Approximation | Failure probability |
|---|---|---|
| Unweighted | 0.71295 | At most delta |
| Bounded positive integers | 0.71295 | At most delta |
| Arbitrary positive rationals | 0.71295 minus epsilon | At most delta |

The algorithms use one pass in uniformly random original-edge order. Their
confidence parameters, acquisition histories, exact/abort branches, weight
clipping, and weight-window retirement are instantiated in the proofs.
The public theorems do not assume an algorithm-success or profile-feasibility
conclusion. The unknown stream length and weight range are handled by the
defined algorithms.

For a known vertex-universe bound n >= 2 and 0 < delta < 1, let
Lambda = 1 + log(n/delta). Unweighted space is O(n Lambda^6) bits.
For positive rational weights, space is O_epsilon(n Lambda^6(Bwt + Lambda))
bits, where Bwt bounds the binary length of each input numerator and
denominator. The formal development proves the underlying record and
metadata bounds and finite component encodings; the paper gives the bit
accounting and external-solver implementation argument. For fixed epsilon,
running time is polynomial in the encoded input size. Standalone bounded
integer unfolding is pseudopolynomial in the maximum integer weight.

Start with [Algorithms.lean](RandomOrderMatching/Algorithms.lean) and
[HistoricalDeletion.lean](RandomOrderMatching/HistoricalDeletion.lean). The
[theorem map](THEOREM_MAP.md) relates the paper statements to these entry
points. The library is organized by mathematical subject: graph structure,
historical deletion, unfolding, probability, streaming, weights, resources,
and the exact certificate. `SOURCE_MANIFEST.json` records all selected
entry points and their exact local dependency closure.

## Verification

See the [verification record](VERIFICATION_STATUS.md) for the completed
build, axiom audit, and statement comparison.

The Lean toolchain and mathlib revision are pinned. With `elan` installed:

```sh
lake exe cache get
python3 verify.py
```

The axiom audit checks every declaration owned by the imported project
modules, including generated declarations. It traverses raw kernel types
and bodies, retaining cyclic dependencies through inductive and recursor
definitions. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted. No admission, new axiom or `native_decide`
certifies the result. `verify.py` builds local modules sequentially and saves
source hashes, compiler logs and the final axiom audit under `verification/`.
An interrupted check can be resumed with `python3 verify.py --resume`;
unchanged source, compiler, external proof artifacts, and direct dependency
outputs are checked before reuse. Checkpoints are written atomically; an unreadable or malformed JSON
checkpoint triggers a rebuild. Standard `lake build` followed by `lake env lean AuditAxioms.lean`
is also supported.

## Exact numerical certificate

```sh
python3 certificates/degree_profile/verify.py
```

This independent checker uses only Python's standard library. It reconstructs
all 996,325 semantic columns and checks them with exact rational arithmetic;
it does not import an optimizer or the producer's matrix builder. The
certificate value is
`2896371675910694789 / 4062500000000000000`. The proved error and prefix
losses leave more than 0.71295. The Lean development separately proves the
actual graph-to-profile map and the complete probability composition.

The degree profile has 152 intervals and includes benchmark edges with both
endpoints in the cover. The certificate data and checker accompany the source
package; floating-point experiments are not used as proof.

## Formal scope

The proofs establish the mathematical state transitions, matching validity,
approximation guarantees, actual stored-record/metadata bounds and finite
component encodings. This is not an extracted executable implementation.
A packed state serializer, heap allocator, and the machine-level complexity
of the standard exact matching solver are outside the formalization. The
paper gives the implementation correspondence and cites the solver's space
and running-time guarantees explicitly.

## AI methodology

OpenAI Codex, using the Astra model, materially supported literature discovery,
proof development and review, exact experiments, Lean formalization, and
drafting. Fable 5.2 also contributed conjectures, proof ideas, and mathematical
feedback. The theorem map and verification records specify what was checked.
