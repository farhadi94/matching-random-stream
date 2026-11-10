# Matching in random-order streams

Lean proofs and exact certificates accompanying work by Alireza Farhadi
and Mohammadtaghi Hajiaghayi.

This is an in-progress artifact. The current entry point verifies selected
components of the intended paper. **It does not yet prove the complete
random-order streaming algorithm**, its probability guarantee, or its total
space bound.

## Included verified components

- Historical weighted deletion and copied-transfer theorems on actual
  graphs, including overlapping original parents of a selected copied matching.
- The concrete rational repair-profile certificate, with value
  `2896371675910694789 / 4062500000000000000`, and the arithmetic showing
  that the specified error and prefix losses leave more than `0.71295`.
- Deterministic execution of weighted phases, retained matching output,
  per-phase record bounds, and execution-to-repair composition with explicit
  upstream graph and probability-event hypotheses.

The certificate theorem requires actual profile feasibility; the execution
theorem requires its stated structural and event inputs. Full acquisition,
probability, graph-to-profile and streaming-wrapper composition is ongoing.
The source manifest lists only the dependency closure of these entry points.
Historical round numbers in module names are identifiers, not extra claims.

## Verify the Lean proofs

The toolchain and mathlib revision are pinned in `lean-toolchain` and
`lake-manifest.json`. With Lean's `elan` installed:

```sh
lake exe cache get
lake build
lake env lean AuditAxioms.lean
```

The axiom audit checks every declaration from the imported project modules,
including generated declarations. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. No admission, additional axiom or `native_decide`
is used to certify the numerical result.

## Independently verify the rational certificate

```sh
python3 certificates/internal152/verify.py
```

This check uses only Python's standard library and reconstructs all
996,325 semantic columns using exact rational arithmetic. It does not
import an optimizer or the producer's matrix builder. A passing certificate
alone is not a proof of the streaming algorithm; graph feasibility and
probability are separate mathematical obligations.

## AI methodology

OpenAI Codex, using the Astra model, materially supported literature discovery,
proof development and review,
exact experiments, Lean formalization, and drafting. The final paper will
describe the full verification coverage. The current scope is stated above.
