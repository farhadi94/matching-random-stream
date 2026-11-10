import RobustMatching.R7GraphFractional

/-! An explicit bridge from finite nonnegative bipartite matrices to actual
two-vertex-edge graphs and integral matchings. -/

noncomputable section
open scoped BigOperators
open Classical

namespace RobustMatching.R7GraphMatrix
open RobustMatching.R2Cut RobustMatching.R7GraphKonig

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def edgeOf (p : L × R) : Edge (L ⊕ R) :=
  ⟨{Sum.inl p.1, Sum.inr p.2}, by simp⟩

theorem edgeOf_injective : Function.Injective (edgeOf : L × R → Edge (L ⊕ R)) := by
  intro p q heq
  have hv := congrArg Subtype.val heq
  have hl : Sum.inl p.1 ∈ (edgeOf q).val := by rw [← hv]; simp [edgeOf]
  have hr : Sum.inr p.2 ∈ (edgeOf q).val := by rw [← hv]; simp [edgeOf]
  exact Prod.ext (by simpa [edgeOf] using hl) (by simpa [edgeOf] using hr)

def pairs (adj : L → R → Prop) : Finset (L × R) :=
  Finset.univ.filter fun p => adj p.1 p.2

def graphEdges (adj : L → R → Prop) : Graph (L ⊕ R) :=
  (pairs adj).image edgeOf

theorem graphEdges_colorable (adj : L → R → Prop) :
    (simpleGraph (graphEdges adj)).Colorable 2 := by
  apply colorable_of_cut (graphEdges adj) (Sum.elim (fun _ => false) (fun _ => true))
  intro e he u hu v hv hne
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
  simp only [edgeOf, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

def edgeWeight (adj : L → R → Prop) (f : L → R → ℝ) (e : Edge (L ⊕ R)) : ℝ :=
  ∑ p ∈ pairs adj, if edgeOf p = e then f p.1 p.2 else 0

theorem edgeWeight_edgeOf (adj : L → R → Prop) (f : L → R → ℝ)
    (p : L × R) (hp : p ∈ pairs adj) : edgeWeight adj f (edgeOf p) = f p.1 p.2 := by
  simp only [edgeWeight, edgeOf_injective.eq_iff]
  simp [hp]

theorem graph_weight_sum (adj : L → R → Prop) (f : L → R → ℝ)
    (hsupp : ∀ l r, ¬adj l r → f l r = 0) :
    (∑ e ∈ graphEdges adj, edgeWeight adj f e) = ∑ l, ∑ r, f l r := by
  rw [graphEdges, Finset.sum_image (edgeOf_injective.injOn)]
  calc
    (∑ p ∈ pairs adj, edgeWeight adj f (edgeOf p)) = ∑ p ∈ pairs adj, f p.1 p.2 :=
      Finset.sum_congr rfl (fun p hp => edgeWeight_edgeOf adj f p hp)
    _ = ∑ p : L × R, f p.1 p.2 := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro p _ hp
      apply hsupp p.1 p.2
      simpa [pairs] using hp
    _ = ∑ l, ∑ r, f l r := Fintype.sum_prod_type _

theorem graph_weight_load (adj : L → R → Prop) (f : L → R → ℝ)
    (hf : ∀ l r, 0 ≤ f l r)
    (hrow : ∀ l, (∑ r, f l r) ≤ 1) (hcol : ∀ r, (∑ l, f l r) ≤ 1) :
    ∀ v : L ⊕ R,
      (∑ e ∈ graphEdges adj, if v ∈ e.val then edgeWeight adj f e else 0) ≤ 1 := by
  intro v
  rw [graphEdges, Finset.sum_image edgeOf_injective.injOn]
  have heq : (∑ p ∈ pairs adj,
      if v ∈ (edgeOf p).val then edgeWeight adj f (edgeOf p) else 0) =
      ∑ p ∈ pairs adj, if v ∈ (edgeOf p).val then f p.1 p.2 else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [edgeWeight_edgeOf adj f p hp]
  rw [heq]
  have hle : (∑ p ∈ pairs adj, if v ∈ (edgeOf p).val then f p.1 p.2 else 0) ≤
      ∑ p : L × R, if v ∈ (edgeOf p).val then f p.1 p.2 else 0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro p _ _
    split_ifs
    · exact hf p.1 p.2
    · exact le_rfl
  apply hle.trans
  cases v with
  | inl l =>
      simpa [Fintype.sum_prod_type, edgeOf] using hrow l
  | inr r =>
      simpa [Fintype.sum_prod_type, edgeOf] using hcol r

/-- A feasible finite fractional matrix has an actual integral matching
in precisely its declared bipartite support, of at least its total mass. -/
theorem matrix_rounding (adj : L → R → Prop) (f : L → R → ℝ)
    (hf : ∀ l r, 0 ≤ f l r) (hsupp : ∀ l r, ¬adj l r → f l r = 0)
    (hrow : ∀ l, (∑ r, f l r) ≤ 1) (hcol : ∀ r, (∑ l, f l r) ≤ 1) :
    ∃ M ⊆ graphEdges adj, Matching M ∧ (∑ l, ∑ r, f l r) ≤ (M.card : ℝ) := by
  have hw : ∀ e ∈ graphEdges adj, 0 ≤ edgeWeight adj f e := by
    intro e _
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact hf p.1 p.2
    · exact le_rfl
  obtain ⟨M, hMG, hM, hmass⟩ := fractional_rounding (graphEdges adj)
    (graphEdges_colorable adj) (edgeWeight adj f) hw (graph_weight_load adj f hf hrow hcol)
  rw [graph_weight_sum adj f hsupp] at hmass
  exact ⟨M, hMG, hM, hmass⟩

theorem matrix_le_rank (adj : L → R → Prop) (f : L → R → ℝ)
    (hf : ∀ l r, 0 ≤ f l r) (hsupp : ∀ l r, ¬adj l r → f l r = 0)
    (hrow : ∀ l, (∑ r, f l r) ≤ 1) (hcol : ∀ r, (∑ l, f l r) ≤ 1) :
    (∑ l, ∑ r, f l r) ≤ (rank (graphEdges adj) : ℝ) := by
  obtain ⟨M, hMG, hM, hmass⟩ := matrix_rounding adj f hf hsupp hrow hcol
  exact hmass.trans (by exact_mod_cast matching_card_le_rank hMG hM)

end RobustMatching.R7GraphMatrix

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphMatrix.matrix_rounding
