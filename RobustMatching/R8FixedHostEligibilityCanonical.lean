import RobustMatching.R8FixedHostEligibility
import RobustMatching.R8FixedHostBenchmarkBounds
import RobustMatching.R8PhaseEmbeddingCanonical

/-! Instantiate the actual underfull suffix store with canonical batches.
The frozen H may contain only some copies of its original parents. -/
noncomputable section
open Classical
set_option linter.unusedSectionVars false
namespace RobustMatching.R8FixedHostEligibility
open RobustMatching.R2Cut RobustMatching.R8Acquisition
open RobustMatching.R8FixedHostBenchmark RobustMatching.R8PhaseEmbedding
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem copiedBenchmark_subset_suffix (W : ℕ) (w : Edge V → ℕ) (hw : ∀e, w e ≤ W)
    (M : Graph V) (suffix : List (Edge V)) (hsub : M ⊆ suffix.toFinset) :
    copiedBenchmark W w hw M ⊆ seenCopies (canonicalCopies W w hw) suffix := by
  apply seenCopies_mono
  simpa using hsub

theorem canonical_available_parent (W : ℕ) (w : Edge V → ℕ) (hw : ∀e, w e ≤ W)
    (fallback : Edge V) (lower : ℕ) (H : Graph (V × Fin W))
    (suffix : List (Edge V)) {f : Edge (V × Fin W)}
    (hf : f ∈ availableSuffix lower H (canonicalCopies W w hw) suffix) :
    canonicalParent W fallback f ∈ referenceParents (canonicalParent W fallback) H ∨
      (eligibleOriginal lower H (canonicalCopies W w hw) (canonicalParent W fallback f) ∧
        canonicalParent W fallback f ∈ suffix) := by
  simpa only [canonicalBatchModel] using
    availableSuffix_parent lower H (canonicalBatchModel W w hw fallback) suffix hf

theorem canonical_benchmark_missing_lower (W : ℕ) (w : Edge V → ℕ) (hw : ∀e, w e ≤ W)
    (lower : ℕ) (H : Graph (V × Fin W)) (M : Graph V)
    (suffix : List (Edge V)) (hsub : M ⊆ suffix.toFinset) :
    ∀f ∈ copiedBenchmark W w hw M \ availableSuffix lower H (canonicalCopies W w hw) suffix,
      lower ≤ edgeDegree H f :=
  missing_subgraph_lower lower H (canonicalCopies W w hw) suffix (copiedBenchmark W w hw M)
    (copiedBenchmark_subset_suffix W w hw M suffix hsub)

/-- Canonical consistency is derived from actual prior/suffix provenance. -/
theorem canonical_available_consistent (W : ℕ) (w : Edge V → ℕ) (hw : ∀e, w e ≤ W)
    (fallback : Edge V) (lower : ℕ) (H : Graph (V × Fin W))
    (prior suffix : List (Edge V)) (hH : H ⊆ seenCopies (canonicalCopies W w hw) prior) :
    ConsistentCopies W w (canonicalParent W fallback)
      (availableSuffix lower H (canonicalCopies W w hw) suffix) := by
  apply (canonical_copies_consistent W w hw fallback (prior ++ suffix)).mono
  have heq : seenCopies (canonicalCopies W w hw) (prior ++ suffix) =
      seenCopies (canonicalCopies W w hw) prior ∪ seenCopies (canonicalCopies W w hw) suffix := by
    simp [seenCopies]
  rw [heq]
  exact (availableSuffix_subset lower H (canonicalCopies W w hw) suffix).trans
    (Finset.union_subset_union_left hH)

/-- Equivalently, a frozen canonical H consistency certificate composes with
all underfull suffix copies; no full-parent completion of H is required. -/
theorem canonical_available_consistent_of_frozen (W : ℕ) (w : Edge V → ℕ) (hw : ∀e, w e ≤ W)
    (fallback : Edge V) (lower : ℕ) (H : Graph (V × Fin W))
    (suffix : List (Edge V)) (hH : ConsistentCopies W w (canonicalParent W fallback) H) :
    ConsistentCopies W w (canonicalParent W fallback)
      (availableSuffix lower H (canonicalCopies W w hw) suffix) := by
  have hU := (canonical_copies_consistent W w hw fallback suffix).mono
    (underfullSuffix_subset lower H (canonicalCopies W w hw) suffix)
  constructor
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hH.projection e he
    · exact hU.projection e he
  · intro e he u hu v hv hne
    rcases Finset.mem_union.mp he with he | he
    · exact hH.index e he u hu v hv hne
    · exact hU.index e he u hu v hv hne

end RobustMatching.R8FixedHostEligibility
