import RandomOrderMatching.Analysis.FixedHost.CopiedBenchmark

/-! Actual suffix provenance and size bounds for the canonical copied
benchmark. Physical suffix labels need not be distinct for these bounds. -/
noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Analysis.FixedHost.Benchmark
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem copiedBenchmark_card_le (M : Graph V) (hM : Matching M) (W : ℕ)
    (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W) :
    (copiedBenchmark W w hw M).card ≤ W * M.card := by
  rw [(copiedBenchmark_exact M hM W w hw).2]
  calc
    (∑ e ∈ M, w e) ≤ ∑ _e ∈ M, W := Finset.sum_le_sum fun e _ => hw e
    _ = W * M.card := by simp [Nat.mul_comm]

theorem copiedBenchmark_parent_in_suffix (M : Graph V) (W : ℕ)
    (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W) (fallback : Edge V)
    (suffix : List (Edge V)) (hsub : M ⊆ suffix.toFinset)
    {f : Edge (V × Fin W)} (hf : f ∈ copiedBenchmark W w hw M) :
    canonicalParent W fallback f ∈ suffix := by
  exact List.mem_toFinset.mp (hsub (copiedBenchmark_parent_mem M W w hw fallback hf))

theorem copiedBenchmark_card_le_suffix (M : Graph V) (hM : Matching M) (W : ℕ)
    (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W)
    (suffix : List (Edge V)) (hsub : M ⊆ suffix.toFinset) :
    (copiedBenchmark W w hw M).card ≤ W * suffix.length := by
  apply (copiedBenchmark_card_le M hM W w hw).trans
  apply Nat.mul_le_mul_left
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le suffix)

theorem copiedBenchmark_parent_in_labels {B : Type*} [Fintype B]
    (M : Graph V) (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W)
    (fallback : Edge V) (original : B → Edge V)
    (hsub : M ⊆ Finset.univ.image original)
    {f : Edge (V × Fin W)} (hf : f ∈ copiedBenchmark W w hw M) :
    ∃ b : B, original b = canonicalParent W fallback f := by
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp
    (hsub (copiedBenchmark_parent_mem M W w hw fallback hf))
  exact ⟨b,hb⟩

theorem copiedBenchmark_card_le_labels {B : Type*} [Fintype B]
    (M : Graph V) (hM : Matching M) (W : ℕ)
    (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W) (original : B → Edge V)
    (hsub : M ⊆ Finset.univ.image original) :
    (copiedBenchmark W w hw M).card ≤ W * Fintype.card B := by
  apply (copiedBenchmark_card_le M hM W w hw).trans
  apply Nat.mul_le_mul_left
  exact (Finset.card_le_card hsub).trans (by simpa using Finset.card_image_le (s:=Finset.univ) (f:=original))

end RandomOrderMatching.Analysis.FixedHost.Benchmark
