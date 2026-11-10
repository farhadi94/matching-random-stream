import RandomOrderMatching.Probability.ClockCoupling.Transfer

/-! Normalized finite means connect the coupling's exact uniform marginal
to conditional suffix-cylinder laws on arbitrary remaining label sets. -/
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Probability.ClockCoupling

theorem integral_uniformOrder {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) :
    (∫ σ, f σ ∂uniformOrder n) =
      (∑ σ, f σ) / Fintype.card (Equiv.Perm (Fin n)) := by
  rw [uniformOrder, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem integral_uniformOrder_reindex {n : ℕ} {B : Type*} [Fintype B]
    (e : Fin n ≃ B) (f : Equiv.Perm B → ℝ) :
    (∫ σ, f (e.permCongr σ) ∂uniformOrder n) =
      (∑ σ : Equiv.Perm B, f σ) / Fintype.card (Equiv.Perm B) := by
  rw [integral_uniformOrder, Equiv.sum_comp]
  rw [Fintype.card_congr e.permCongr]

theorem uniformOrder_real {n : ℕ} (S : Set (Equiv.Perm (Fin n))) :
    (uniformOrder n).real S =
      ((Finset.univ.filter fun σ => σ ∈ S).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) := by
  rw [measureReal_def, uniformOrder,
    PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite S).measurableSet]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Fintype.card_subtype]

end RandomOrderMatching.Probability.ClockCoupling
