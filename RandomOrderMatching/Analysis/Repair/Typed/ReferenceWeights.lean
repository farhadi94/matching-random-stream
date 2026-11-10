import RandomOrderMatching.Analysis.Repair.Typed.Availability
import RandomOrderMatching.Analysis.Support.CappedIncidence

/-! The typed matrices use the actual capped reference-incidence weights.
Their nonnegativity, support, shared row capacity and low-outside bound
follow from the existing graph-derived SupportData interface. -/
noncomputable section
open scoped BigOperators
open Classical

namespace RandomOrderMatching.Analysis.Repair.Typed
open RandomOrderMatching.Analysis.Repair.Reference

variable {C O : Type*} [Fintype C] [Fintype O]

def referenceWeight (adj : O → C → Prop) (β δ : ℝ) (a : O → ℝ) : C → O → ℝ :=
  fun c x => RandomOrderMatching.Analysis.Support.cappedWeight adj β δ a x c

theorem referenceWeight_nonneg (adj : O → C → Prop)
    {β δ : ℝ} (a : O → ℝ) (hβ : 0 < β) (hδ : 0 < δ) :
    ∀ c x, 0 ≤ referenceWeight adj β δ a c x := by
  intro c x
  exact RandomOrderMatching.Analysis.Support.cappedWeight_nonneg hβ hδ x c

omit [Fintype C] [Fintype O] in
theorem referenceWeight_supported (adj : O → C → Prop)
    (β δ : ℝ) (a : O → ℝ) :
    ∀ c x, ¬adj x c → referenceWeight adj β δ a c x = 0 := by
  intro c x hh
  simp [referenceWeight, RandomOrderMatching.Analysis.Support.cappedWeight, hh]

theorem referenceWeight_row_capacity [DecidableEq C] [DecidableEq O]
    (adj : O → C → Prop) {β δ : ℝ} (a : O → ℝ) (dc : C → ℝ)
    (h : SupportData adj β a dc) :
    ∀ c, (∑ x, referenceWeight adj β δ a c x) ≤ 1 := by
  intro c
  exact RandomOrderMatching.Analysis.Support.capped_column_le_one h c

theorem referenceWeight_column_exact [DecidableEq C] [DecidableEq O]
    (adj : O → C → Prop) {β δ : ℝ} (a : O → ℝ) (dc : C → ℝ)
    (h : SupportData adj β a dc) (hδ : 0 < δ) (x : O) :
    (∑ c, referenceWeight adj β δ a c x) = a x / max δ (1-a x) := by
  exact RandomOrderMatching.Analysis.Support.capped_row_exact h hδ x

theorem referenceWeight_low_column [DecidableEq C] [DecidableEq O]
    (adj : O → C → Prop) {β δ : ℝ} (a : O → ℝ) (dc : C → ℝ)
    (h : SupportData adj β a dc) (hδ : 0 < δ) (x : O)
    (hx : a x ≤ 1/2) :
    (∑ c, referenceWeight adj β δ a c x) ≤ 1 := by
  rw [referenceWeight_column_exact adj a dc h hδ x]
  have hm : 0 < max δ (1-a x) := lt_of_lt_of_le hδ (le_max_left _ _)
  apply (div_le_iff₀ hm).2
  have hh := le_max_right δ (1-a x)
  nlinarith

theorem referenceWeight_edge_cap (adj : O → C → Prop)
    {β δ : ℝ} (a : O → ℝ) (hβ : 0 < β) (hδ : 0 < δ) :
    ∀ c x, referenceWeight adj β δ a c x ≤ 1/(β*δ) := by
  intro c x
  exact RandomOrderMatching.Analysis.Support.cappedWeight_le_edge_cap hβ hδ x c

end RandomOrderMatching.Analysis.Repair.Typed
