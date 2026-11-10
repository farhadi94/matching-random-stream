import RandomOrderMatching.Probability.ClockCoupling.Order
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Prod

/-! Exact finite coupling of a uniform stream permutation and independent
categorical clocks on original labels. -/
noncomputable section
set_option maxHeartbeats 800000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RandomOrderMatching.Probability.ClockCoupling
open RandomOrderMatching.Analysis.Repair.Probability

instance permMeasurableSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
instance permMeasurableSingleton (n : ℕ) : MeasurableSingletonClass (Equiv.Perm (Fin n)) :=
  ⟨fun _ => trivial⟩

def uniformOrder (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure

instance (n : ℕ) : IsProbabilityMeasure (uniformOrder n) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)

lemma uniform_pmf_equiv {A : Type*} [Fintype A] [Nonempty A] (e : A ≃ A) :
    (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype A := by
  ext b
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  have he (a : A) : b = e a ↔ e.symm b = a := by
    constructor
    · intro h; rw [h]; simp
    · intro h; rw [← h]; simp
  simp_rw [he]
  simp

lemma uniformOrder_equiv {n : ℕ} (e : Equiv.Perm (Equiv.Perm (Fin n))) :
    MeasurePreserving e (uniformOrder n) (uniformOrder n) := by
  refine ⟨measurable_of_finite _, ?_⟩
  rw [uniformOrder, PMF.toMeasure_map e _ (measurable_of_finite _), uniform_pmf_equiv]

def orderRelabel {n : ℕ} (z : Fin n → Clock) : Equiv.Perm (Equiv.Perm (Fin n)) where
  toFun := streamOrder z
  invFun := fun σ => (categorySort z).symm.trans σ
  left_inv := by intro π; ext i; simp [streamOrder]
  right_inv := by intro π; ext i; simp [streamOrder]

lemma streamOrder_preserving {n : ℕ} (z : Fin n → Clock) :
    MeasurePreserving (streamOrder z) (uniformOrder n) (uniformOrder n) :=
  uniformOrder_equiv (orderRelabel z)

lemma labelClocks_preserving {n : ℕ} (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun z => labelClocks z π)
      (experiment (B := Fin n)) (experiment (B := Fin n)) := by
  convert (measurePreserving_piCongrLeft (fun _ : Fin n => clockMeasure) π) using 1
  · funext z b
    simp [labelClocks, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft,
      Equiv.piCongrLeft', Equiv.symm_apply_apply]
  · rfl
  · rfl

def coupling (n : ℕ) : Measure ((Fin n → Clock) × Equiv.Perm (Fin n)) :=
  (experiment (B := Fin n)).prod (uniformOrder n)

instance (n : ℕ) : IsProbabilityMeasure (coupling n) :=
  inferInstanceAs (IsProbabilityMeasure ((experiment (B := Fin n)).prod (uniformOrder n)))

def coupledOrder {n : ℕ} (s : (Fin n → Clock) × Equiv.Perm (Fin n)) :=
  streamOrder s.1 s.2

def coupledClocks {n : ℕ} (s : (Fin n → Clock) × Equiv.Perm (Fin n)) :=
  labelClocks s.1 s.2

/-- The actual stream order is exactly uniform, without a conditioning
assumption about its categorical clocks. -/
theorem coupledOrder_preserving (n : ℕ) :
    MeasurePreserving (coupledOrder (n := n)) (coupling n) (uniformOrder n) := by
  have hs := (MeasurePreserving.id (experiment (B := Fin n))).skew_product
    (g := fun z π => streamOrder z π) (measurable_of_finite _)
    (Filter.Eventually.of_forall fun z => (streamOrder_preserving z).map_eq)
  exact measurePreserving_snd.comp hs

/-- The clock vector has exactly the finite independent original-label
product distribution used by the repair theorems. -/
theorem coupledClocks_preserving (n : ℕ) :
    MeasurePreserving (coupledClocks (n := n)) (coupling n)
      (experiment (B := Fin n)) := by
  have hs := (MeasurePreserving.id (uniformOrder n)).skew_product
    (g := fun π z => labelClocks z π) (measurable_of_finite _)
    (Filter.Eventually.of_forall fun π => (labelClocks_preserving π).map_eq)
  exact (measurePreserving_snd.comp hs).comp Measure.measurePreserving_swap

/-- The two marginals are coupled so that category order agrees with the
actual stream chronology, for every outcome. -/
theorem coupled_chronology {n : ℕ} (s : (Fin n → Clock) × Equiv.Perm (Fin n)) :
    Monotone (fun i => coupledClocks s (coupledOrder s i)) :=
  coupled_order_monotone s.1 s.2

end RandomOrderMatching.Probability.ClockCoupling
