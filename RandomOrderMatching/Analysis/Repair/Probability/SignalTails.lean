import RandomOrderMatching.Analysis.Repair.Probability.Signals

noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair.Probability

variable {B T : Type*} [Fintype B] [Fintype T]

def signalSum (parent : T → B) (s : T → Signal) (a : T → ℝ) (z : B → Clock) : ℝ :=
  ∑ i, a i * signalValue (s i) (z (parent i))

def signalExpectation (s : T → Signal) (a : T → ℝ) : ℝ :=
  ∑ i, a i * signalMean (s i)

def signalRanges (s : T → Signal) (a : T → ℝ) (i : T) : ℝ :=
  a i * signalRange (s i)

lemma integral_centered_signal (s : Signal) (a : ℝ) :
    (∫ z, a*(signalValue s z-signalBase s) ∂clockMeasure) =
      a*(signalMean s-signalBase s) := by
  have h := integral_signal s
  rw [integral_clock] at h ⊢
  rw [← h]
  ring

lemma scaled_signal_bounds (s : Signal) {a : ℝ} (ha : 0 ≤ a) (z : Clock) :
    a*(signalValue s z-signalBase s) ∈ Set.Icc 0 (a*signalRange s) := by
  have h := signal_range s z
  exact ⟨mul_nonneg ha h.1, mul_le_mul_of_nonneg_left h.2 ha⟩

/-- Every summand is evaluated at its original parent's categorical clock. -/
theorem signal_upper_tail (parent : T → B) (s : T → Signal) (a : T → ℝ)
    (ha : ∀ i, 0 ≤ a i) {t : ℝ} (ht : 0 ≤ t) :
    (experiment (B := B)).real {z | t ≤ signalSum parent s a z-signalExpectation s a} ≤
      Real.exp (-2*t^2 / ∑ b, (blockRange parent (signalRanges s a) b)^2) := by
  have h := batch_upper_tail parent
    (fun i z => a i*(signalValue (s i) z-signalBase (s i)))
    (signalRanges s a) (fun i z => scaled_signal_bounds (s i) (ha i) z) ht
  simp_rw [integral_centered_signal] at h
  simp only [mul_sub, Finset.sum_sub_distrib, sub_sub_sub_cancel_right] at h
  exact h

theorem signal_lower_tail (parent : T → B) (s : T → Signal) (a : T → ℝ)
    (ha : ∀ i, 0 ≤ a i) {t : ℝ} (ht : 0 ≤ t) :
    (experiment (B := B)).real {z | t ≤ signalExpectation s a-signalSum parent s a z} ≤
      Real.exp (-2*t^2 / ∑ b, (blockRange parent (signalRanges s a) b)^2) := by
  have h := batch_lower_tail parent
    (fun i z => a i*(signalValue (s i) z-signalBase (s i)))
    (signalRanges s a) (fun i z => scaled_signal_bounds (s i) (ha i) z) ht
  simp_rw [integral_centered_signal] at h
  simp only [mul_sub, Finset.sum_sub_distrib, sub_sub_sub_cancel_right] at h
  exact h

lemma signalRange_nonneg (s : Signal) : 0 ≤ signalRange s := by
  cases s <;> norm_num [signalRange]

lemma signalRange_le_one (s : Signal) : signalRange s ≤ 1 := by
  cases s <;> norm_num [signalRange]

lemma signalRanges_nonneg (s : T → Signal) (a : T → ℝ) (ha : ∀i,0≤a i) (i : T) :
    0 ≤ signalRanges s a i := mul_nonneg (ha i) (signalRange_nonneg (s i))

lemma signalRanges_le (s : T → Signal) (a : T → ℝ) (ha : ∀i,0≤a i) (i : T) :
    signalRanges s a i ≤ a i := by
  exact (mul_le_mul_of_nonneg_left (signalRange_le_one (s i)) (ha i)).trans_eq (mul_one _)

end RandomOrderMatching.Analysis.Repair.Probability
