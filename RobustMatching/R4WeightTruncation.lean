import Mathlib.Tactic
import Mathlib.Data.Int.Interval

/-! Continuous truncation for dyadic matching composition. No matching LP
existence theorem or approximation conclusion is postulated. -/
open scoped BigOperators
namespace RobustMatching.R4WeightTruncation

noncomputable def raw (L x : ℝ) : ℝ := max 0 (min (4*x-L) (x+L/2))
noncomputable def trunc (L U x : ℝ) : ℝ := min U (raw L x)
theorem raw_nonneg (L x : ℝ) : 0 ≤ raw L x := le_max_left _ _
theorem trunc_nonneg {L U x : ℝ} (hU : 0 ≤ U) : 0 ≤ trunc L U x :=
  le_min hU (raw_nonneg L x)
theorem raw_monotone (L : ℝ) : Monotone (raw L) := by
  intro a b hab
  exact max_le_max le_rfl (min_le_min (by linarith) (by linarith))
theorem trunc_monotone (L U : ℝ) : Monotone (trunc L U) := by
  intro a b hab
  exact min_le_min le_rfl (raw_monotone L hab)
theorem trunc_zero {L U : ℝ} (hL : 0 ≤ L) (hU : 0 ≤ U) : trunc L U 0 = 0 := by
  unfold trunc raw
  have : min (4*(0:ℝ)-L) (0+L/2) ≤ 0 := (min_le_left _ _).trans (by linarith)
  rw [max_eq_left this, min_eq_right hU]

/-- A low price loses at most L/4 before the upper cap. -/
theorem raw_loss {L x : ℝ} (hL : 0 ≤ L) : x - L/4 ≤ raw L x := by
  unfold raw
  by_cases hx : x ≤ L/4
  · exact (by linarith : x-L/4 ≤ 0).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    apply le_min <;> linarith
theorem raw_high {L x : ℝ} (hL : 0 ≤ L) (hx : L/2 ≤ x) : raw L x = x+L/2 := by
  unfold raw
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]
theorem raw_low {L x : ℝ} (hx : x ≤ L/2) : 4*x-L ≤ raw L x := by
  unfold raw
  rw [min_eq_left (by linarith)]
  exact le_max_right _ _

/-- Coverage uses exactly three prices: the endpoints and the common blossom total. -/
theorem raw_three_cover {L a b c w : ℝ} (hL : 0 ≤ L)
    (hwL : L ≤ w) (hw : w ≤ a+b+c) : w ≤ raw L a + raw L b + raw L c := by
  by_cases ha : L/2 ≤ a
  · rw [raw_high hL ha]
    linarith [raw_loss (x := b) hL, raw_loss (x := c) hL]
  by_cases hb : L/2 ≤ b
  · rw [raw_high hL hb]
    linarith [raw_loss (x := a) hL, raw_loss (x := c) hL]
  by_cases hc : L/2 ≤ c
  · rw [raw_high hL hc]
    linarith [raw_loss (x := a) hL, raw_loss (x := b) hL]
  · linarith [raw_low (le_of_not_ge ha), raw_low (le_of_not_ge hb), raw_low (le_of_not_ge hc)]
theorem three_price_cover {L U a b c w : ℝ} (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hwL : L ≤ w) (hwU : w ≤ U) (hw : w ≤ a+b+c) :
    w ≤ trunc L U a + trunc L U b + trunc L U c := by
  by_cases ha : U ≤ raw L a
  · have ha' : trunc L U a = U := min_eq_left ha
    rw [ha']
    linarith [trunc_nonneg (L := L) (x := b) hU, trunc_nonneg (L := L) (x := c) hU]
  by_cases hb : U ≤ raw L b
  · have hb' : trunc L U b = U := min_eq_left hb
    rw [hb']
    linarith [trunc_nonneg (L := L) (x := a) hU, trunc_nonneg (L := L) (x := c) hU]
  by_cases hc : U ≤ raw L c
  · have hc' : trunc L U c = U := min_eq_left hc
    rw [hc']
    linarith [trunc_nonneg (L := L) (x := a) hU, trunc_nonneg (L := L) (x := b) hU]
  · simpa [trunc, min_eq_right (le_of_not_ge ha), min_eq_right (le_of_not_ge hb),
      min_eq_right (le_of_not_ge hc)] using raw_three_cover hL hwL hw

/-- Closed endpoint affine pieces are suitable for a finite breakpoint mesh. -/
theorem trunc_piece_zero {L U x : ℝ} (hU : 0 ≤ U) (hx : x ≤ L/4) : trunc L U x = 0 := by
  unfold trunc raw
  have h : min (4*x-L) (x+L/2) ≤ 0 := (min_le_left _ _).trans (by linarith)
  rw [max_eq_left h, min_eq_right hU]
theorem trunc_piece_four {L U x : ℝ} (hLU : L ≤ U)
    (hx : L/4 ≤ x) (hx' : x ≤ L/2) : trunc L U x = 4*x-L := by
  unfold trunc raw
  have hm : min (4*x-L) (x+L/2) = 4*x-L := min_eq_left (by linarith)
  rw [hm, max_eq_right (by linarith), min_eq_right (by linarith)]
theorem trunc_piece_one {L U x : ℝ} (hL : 0 ≤ L)
    (hx : L/2 ≤ x) (hx' : x ≤ U-L/2) : trunc L U x = x+L/2 := by
  rw [trunc, raw_high hL hx, min_eq_right (by linarith)]
theorem trunc_piece_cap {L U x : ℝ} (hL : 0 ≤ L) (hLU : 2*L ≤ U)
    (hx : U-L/2 ≤ x) : trunc L U x = U := by
  unfold trunc raw
  apply min_eq_left
  apply le_trans _ (le_max_right _ _)
  apply le_min <;> linarith

/-- Exact half-open membership count once the edge dyadic exponent is j. -/
theorem window_index_count (j : ℤ) (k : ℕ) : (Finset.Ioc (j-(k:ℤ)) j).card = k := by simp
/-- Integer labels of diameter at most k number at most k+1. -/
theorem integer_diameter_card (S : Finset ℤ) (k : ℕ)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, j-i ≤ (k:ℤ)) : S.card ≤ k+1 := by
  by_cases h : S.Nonempty
  · have hsub : S ⊆ Finset.Icc (S.min' h) (S.min' h + (k:ℤ)) := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S i hi,
        by have := hdiam (S.min' h) (S.min'_mem h) i hi; omega⟩
    have hc := Finset.card_le_card hsub
    have heq : S.min' h + (k:ℤ) + 1 - S.min' h = (k:ℤ)+1 := by ring
    simpa [heq] using hc
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]
end RobustMatching.R4WeightTruncation
#print axioms RobustMatching.R4WeightTruncation.three_price_cover
#print axioms RobustMatching.R4WeightTruncation.trunc_piece_four
#print axioms RobustMatching.R4WeightTruncation.integer_diameter_card
