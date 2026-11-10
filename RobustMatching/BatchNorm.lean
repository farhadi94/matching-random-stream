import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace RobustMatching

/-- Grouping at most `k` real coefficients multiplies their squared-range budget
by at most `k`. This is a deterministic ingredient, not a concentration theorem. -/
theorem batch_sum_sq_le {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (k : ℕ) (hcard : s.card ≤ k) :
    (∑ i ∈ s, c i) ^ 2 ≤ (k : ℝ) * ∑ i ∈ s, c i ^ 2 := by
  calc
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, c i ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard)
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (c i))

end RobustMatching

#print axioms RobustMatching.batch_sum_sq_le
