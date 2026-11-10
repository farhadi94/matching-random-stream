import Mathlib

/-! Finite rounding and selection accounting for sparse weighted decoders.
The exact matching algorithm and its bit complexity are external written inputs.
This theorem applies to actual finite edge sets, or any bounded-cardinality
candidate family; it does not assume the desired approximation conclusion. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R3Precision

def rounded (q w : ℝ) : ℝ := q * (⌊w / q⌋₊ : ℝ)

lemma rounded_bounds {q w : ℝ} (hq : 0 < q) (hw : 0 ≤ w) :
    w - q ≤ rounded q w ∧ rounded q w ≤ w := by
  have hdiv : 0 ≤ w / q := div_nonneg hw hq.le
  have hlow := Nat.sub_one_lt_floor (w / q)
  have hupp := Nat.floor_le hdiv
  have hmul : q * (w / q) = w := by field_simp
  have hl := mul_lt_mul_of_pos_left hlow hq
  have hu := mul_le_mul_of_nonneg_left hupp hq.le
  unfold rounded
  constructor <;> nlinarith

theorem finite_selection {E : Type*} [DecidableEq E]
    (M Q : Finset E) (w : E → ℝ) {q N : ℝ}
    (hq : 0 < q) (hw : ∀ e, 0 ≤ w e)
    (hcard : (M.card : ℝ) ≤ N)
    (hchoice : (∑ e ∈ M, rounded q (w e)) ≤ ∑ e ∈ Q, rounded q (w e)) :
    (∑ e ∈ M, w e) - N*q ≤ ∑ e ∈ Q, w e := by
  have hl := Finset.sum_le_sum (s := M)
    (fun e _ => (rounded_bounds hq (hw e)).1)
  have hu := Finset.sum_le_sum (s := Q)
    (fun e _ => (rounded_bounds hq (hw e)).2)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hl
  have hc := mul_le_mul_of_nonneg_right hcard hq.le
  linarith

theorem relative_selection {E : Type*} [DecidableEq E]
    (M Q : Finset E) (w : E → ℝ) {q N eta : ℝ}
    (hq : 0 < q) (hw : ∀ e, 0 ≤ w e)
    (hcard : (M.card : ℝ) ≤ N)
    (hchoice : (∑ e ∈ M, rounded q (w e)) ≤ ∑ e ∈ Q, rounded q (w e))
    (hscale : N*q ≤ eta*(∑ e ∈ M, w e)) :
    (1-eta)*(∑ e ∈ M, w e) ≤ ∑ e ∈ Q, w e := by
  have hh := finite_selection M Q w hq hw hcard hchoice
  nlinarith

end RobustMatching.R3Precision
#print axioms RobustMatching.R3Precision.rounded_bounds
#print axioms RobustMatching.R3Precision.finite_selection
#print axioms RobustMatching.R3Precision.relative_selection
