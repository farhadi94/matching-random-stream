import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Tactic
import RobustMatching.BatchNorm

/-!
Actual probability-space concentration for the bounded-batch matching analysis.
The probability theorem below uses Mathlib's proved Hoeffding lemma and
independence of coordinates in a finite product measure. It does not assume a
tail inequality. Graph witnesses, sorting clocks, and repair construction are
separate mathematical interfaces, not claimed formalized here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal unitInterval

namespace RobustMatching

/-- Hoeffding for independent bounded random variables, centered by their actual
integrals. No identical-distribution or independence-between-events hypothesis. -/
theorem independent_bounded_upper_tail
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) (X : ι → Ω → ℝ) (a : ι → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 (a i))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, (X i ω - ∫ z, X i z ∂μ)} ≤
      Real.exp (-2 * t ^ 2 / ∑ i ∈ s, a i ^ 2) := by
  have hi : iIndepFun (fun i ω ↦ X i ω - ∫ z, X i z ∂μ) μ :=
    h_indep.comp (fun i x ↦ x - ∫ z, X i z ∂μ) (fun _ ↦ by fun_prop)
  have hg (i) (his : i ∈ s) :
      HasSubgaussianMGF (fun ω ↦ X i ω - ∫ z, X i z ∂μ)
        ((‖a i - 0‖₊ / 2) ^ 2) μ :=
    hasSubgaussianMGF_of_mem_Icc (h_meas i) (h_bound i his)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi hg ht
  convert h using 1
  congr 1
  simp only [NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm,
    NNReal.coe_ofNat, sub_zero, Real.norm_eq_abs]
  have heq : (∑ i ∈ s, (|a i| / 2) ^ 2) = (∑ i ∈ s, a i ^ 2) / 4 := by
    simp_rw [div_pow, sq_abs]
    rw [Finset.sum_div]
    norm_num
  rw [heq]
  ring

/-- Product-space form: one independent coordinate for every fixed batch.
Each `X i` may be any bounded measurable function of that coordinate. -/
theorem product_bounded_upper_tail
    {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X : (i : ι) → Ω i → ℝ) (a : ι → ℝ)
    (h_meas : ∀ i, Measurable (X i))
    (h_bound : ∀ i z, X i z ∈ Set.Icc 0 (a i))
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ).real {ω | t ≤ ∑ i, (X i (ω i) - ∫ z, X i z ∂μ i)} ≤
      Real.exp (-2 * t ^ 2 / ∑ i, a i ^ 2) := by
  have h := independent_bounded_upper_tail (μ := Measure.pi μ) Finset.univ
    (fun i ω ↦ X i (ω i)) a
    (iIndepFun_pi (fun i ↦ (h_meas i).aemeasurable))
    (fun i ↦ ((h_meas i).comp (measurable_pi_apply i)).aemeasurable)
    (fun i _ ↦ ae_of_all _ (fun ω ↦ h_bound i (ω i))) ht
  simpa only [integral_comp_eval (h_meas _).aestronglyMeasurable] using h

/-- A real coefficient activated by its actual uniform clock. -/
noncomputable def clockWeight (p : I) (a : ℝ) (u : I) : ℝ :=
  (Set.Iic p).indicator (fun _ ↦ a) u

theorem clockWeight_measurable (p : I) (a : ℝ) :
    Measurable (clockWeight p a) :=
  measurable_const.indicator measurableSet_Iic

theorem clockWeight_mem_Icc (p : I) {a : ℝ} (ha : 0 ≤ a) (u : I) :
    clockWeight p a u ∈ Set.Icc 0 a := by
  by_cases h : u ≤ p
  · simp [clockWeight, Set.mem_Iic, h, ha]
  · simp [clockWeight, Set.mem_Iic, h, ha]

theorem integral_clockWeight (p : I) (a : ℝ) :
    ∫ u : I, clockWeight p a u = (p : ℝ) * a := by
  change (∫ u : I, (Set.Iic p).indicator (fun _ ↦ a) u) = _
  rw [integral_indicator_const a measurableSet_Iic]
  simp [measureReal_def, ENNReal.toReal_ofReal p.2.1]

/-- Actual independent uniform clocks, with an arbitrary nonnegative coefficient
for each batch. A coefficient may represent several edges sharing one clock. -/
theorem uniform_clock_weighted_upper_tail
    {ι : Type*} [Fintype ι] (p : I) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure I))).real
      {ω | t ≤ ∑ i, (clockWeight p (a i) (ω i) - (p : ℝ) * a i)} ≤
      Real.exp (-2 * t ^ 2 / ∑ i, a i ^ 2) := by
  have h := product_bounded_upper_tail
    (fun _ : ι ↦ (volume : Measure I)) (fun i ↦ clockWeight p (a i)) a
    (fun i ↦ clockWeight_measurable p (a i))
    (fun i u ↦ clockWeight_mem_Icc p (ha i) u) ht
  simpa only [integral_clockWeight] using h

/-- The actual lower-tail estimate, without inferring independence from the
separate upper-tail event. -/
theorem uniform_clock_weighted_lower_tail
    {ι : Type*} [Fintype ι] (p : I) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure I))).real
      {ω | t ≤ ∑ i, ((p : ℝ) * a i - clockWeight p (a i) (ω i))} ≤
      Real.exp (-2 * t ^ 2 / ∑ i, a i ^ 2) := by
  have hm (i) : Measurable (fun u ↦ a i - clockWeight p (a i) u) :=
    measurable_const.sub (clockWeight_measurable p (a i))
  have hb (i) (u : I) : a i - clockWeight p (a i) u ∈ Set.Icc 0 (a i) := by
    have h := clockWeight_mem_Icc p (ha i) u
    constructor <;> linarith [h.1, h.2]
  have hint (i) : Integrable (clockWeight p (a i)) (volume : Measure I) :=
    Integrable.of_mem_Icc 0 (a i) (clockWeight_measurable p (a i)).aemeasurable
      (ae_of_all _ (fun u ↦ clockWeight_mem_Icc p (ha i) u))
  have hi (i) : (∫ u : I, a i - clockWeight p (a i) u) = a i - (p : ℝ) * a i := by
    rw [integral_sub (integrable_const _) (hint i), integral_clockWeight]
    simp
  have h := product_bounded_upper_tail
    (fun _ : ι ↦ (volume : Measure I)) (fun i u ↦ a i - clockWeight p (a i) u)
    a hm hb ht
  simpa only [hi, sub_sub_sub_cancel_left] using h

/-- Summing the Cauchy bound over an arbitrary fixed family of groups. The
grouping may contain negative coefficients; concentration later uses nonnegative
ones to turn the group sum into a range bound. -/
theorem grouped_sum_sq_le
    {ι η : Type*} [Fintype ι] (s : ι → Finset η) (c : η → ℝ)
    (k : ℕ) (hcard : ∀ i, (s i).card ≤ k) :
    (∑ i, (∑ j ∈ s i, c j) ^ 2) ≤
      (k : ℝ) * ∑ i, ∑ j ∈ s i, c j ^ 2 := by
  calc
    _ ≤ ∑ i, (k : ℝ) * ∑ j ∈ s i, c j ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ batch_sum_sq_le (s i) c k (hcard i))
    _ = _ := by rw [Finset.mul_sum]

/-- The root-overload variance budget groups the two endpoints of a missed
matching edge first, and then groups at most k such edges into a batch. This
prevents the incorrect claim that a batch has at most k root endpoints. -/
theorem paired_batch_range_sq_le
    {ι η : Type*} [Fintype ι] (s : ι → Finset η) (f g : η → ℝ)
    (k : ℕ) (hcard : ∀ i, (s i).card ≤ k) {D : ℝ} (hD : 0 ≤ D)
    (hf : ∀ i, ∀ j ∈ s i, f j ∈ Set.Icc 0 D)
    (hg : ∀ i, ∀ j ∈ s i, g j ∈ Set.Icc 0 D) :
    (∑ i, (∑ j ∈ s i, (f j + g j)) ^ 2) ≤
      4 * (k : ℝ) * D ^ 2 * ∑ i, ((s i).card : ℝ) := by
  have hb (i) (j) (hj : j ∈ s i) : (f j + g j) ^ 2 ≤ 4 * D ^ 2 := by
    have hf' := hf i j hj
    have hg' := hg i j hj
    nlinarith [hf'.1, hf'.2, hg'.1, hg'.2]
  calc
    _ ≤ (k : ℝ) * ∑ i, ∑ j ∈ s i, (f j + g j) ^ 2 :=
      grouped_sum_sq_le s (fun j ↦ f j + g j) k hcard
    _ ≤ (k : ℝ) * ∑ i, ∑ _j ∈ s i, 4 * D ^ 2 := by
      gcongr with i hi j hj
      exact hb i j hj
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      ring

/-- Bounded-batch Hoeffding on the actual product of uniform clocks. All
coefficients in one group share its clock. The square-range denominator loses
at most the maximum batch size `k`, with no independence assumed inside groups. -/
theorem uniform_clock_batch_upper_tail
    {ι η : Type*} [Fintype ι] (s : ι → Finset η) (c : η → ℝ)
    (k : ℕ) (hcard : ∀ i, (s i).card ≤ k)
    (hc : ∀ i, ∀ j ∈ s i, 0 ≤ c j) (p : I) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure I))).real
      {ω | t ≤ ∑ i, (clockWeight p (∑ j ∈ s i, c j) (ω i)
        - (p : ℝ) * ∑ j ∈ s i, c j)} ≤
      Real.exp (-2 * t ^ 2 / ((k : ℝ) * ∑ i, ∑ j ∈ s i, c j ^ 2)) := by
  let a : ι → ℝ := fun i ↦ ∑ j ∈ s i, c j
  have ha (i) : 0 ≤ a i := Finset.sum_nonneg (hc i)
  have h := uniform_clock_weighted_upper_tail p a ha ht
  have hsq := grouped_sum_sq_le s c k hcard
  have hn : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg (a i))
  by_cases hz : ∑ i, a i ^ 2 = 0
  · have hzero (i) : a i = 0 := by
      have hh := Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (a i)) |>.mp hz
      exact sq_eq_zero_iff.mp (hh i (Finset.mem_univ i))
    have hc0 (i) (j) (hj : j ∈ s i) : c j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (hc i)).mp (hzero i) j hj
    have hr : (∑ i, ∑ j ∈ s i, c j ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j hj
      simp [hc0 i j hj]
    simpa only [hz, hr, mul_zero, div_zero, Real.exp_zero] using h
  · have hp : 0 < ∑ i, a i ^ 2 := lt_of_le_of_ne hn (Ne.symm hz)
    have hbig : 0 < (k : ℝ) * ∑ i, ∑ j ∈ s i, c j ^ 2 := lt_of_lt_of_le hp hsq
    refine h.trans (Real.exp_le_exp.mpr ?_)
    apply (div_le_div_iff₀ hp hbig).mpr
    nlinarith [sq_nonneg t]

/-- Removing auxiliary proof randomness uses only the deterministic implication
from a successful certificate to actual success. It does not condition actual
clocks on a certificate event. -/
theorem project_away_auxiliary_failure
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (bad : Set Ω) (certificateBad : Set (Ω × Ξ))
    (h : ∀ ω ∈ bad, ∀ ξ, (ω, ξ) ∈ certificateBad) :
    μ.real bad ≤ (μ.prod ν).real certificateBad := by
  calc
    μ.real bad = (μ.prod ν).real (bad ×ˢ Set.univ) := by
      simp [measureReal_def]
    _ ≤ _ := measureReal_mono (by rintro ⟨ω, ξ⟩ ⟨hω, _⟩; exact h ω hω ξ)

noncomputable def clockCount {ι : Type*} [Fintype ι] (p : I) (ω : ι → I) : ℝ :=
  ∑ i, clockWeight p 1 (ω i)

theorem uniform_clock_count_upper_tail
    {ι : Type*} [Fintype ι] (p : I) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure I))).real
      {ω | t ≤ clockCount p ω - (Fintype.card ι : ℝ) * (p : ℝ)} ≤
      Real.exp (-2 * t ^ 2 / (Fintype.card ι : ℝ)) := by
  have h := uniform_clock_weighted_upper_tail (ι := ι) p (fun _ ↦ 1)
    (fun _ ↦ by norm_num) ht
  simpa [clockCount, Finset.sum_sub_distrib] using h

theorem uniform_clock_count_lower_tail
    {ι : Type*} [Fintype ι] (p : I) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure I))).real
      {ω | t ≤ (Fintype.card ι : ℝ) * (p : ℝ) - clockCount p ω} ≤
      Real.exp (-2 * t ^ 2 / (Fintype.card ι : ℝ)) := by
  have h := uniform_clock_weighted_lower_tail (ι := ι) p (fun _ ↦ 1)
    (fun _ ↦ by norm_num) ht
  simpa [clockCount, Finset.sum_sub_distrib] using h

/-- Actual cutoff bracketing on the same clock space. The two failure events
are generally dependent; the proof uses a union bound. The cutoff may be any
fixed real satisfying the margins (integer stream cutoffs are a special case). -/
theorem uniform_clock_cutoff_bracket
    {ι : Type*} [Fintype ι] [Nonempty ι] (α ω : I) {ζ c : ℝ}
    (hζ : 0 ≤ ζ)
    (hleft : ((α : ℝ) + ζ) * (Fintype.card ι : ℝ) ≤ c)
    (hright : c ≤ ((ω : ℝ) - ζ) * (Fintype.card ι : ℝ)) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure I))).real
      {u | c < clockCount α u ∨ clockCount ω u < c} ≤
      2 * Real.exp (-2 * ζ ^ 2 * (Fintype.card ι : ℝ)) := by
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have ht : 0 ≤ ζ * N := mul_nonneg hζ hN.le
  have ha := uniform_clock_count_upper_tail (ι := ι) α ht
  have hb := uniform_clock_count_lower_tail (ι := ι) ω ht
  have hexp : -2 * (ζ * N) ^ 2 / N = -2 * ζ ^ 2 * N := by
    field_simp
  rw [hexp] at ha hb
  have hsub :
      {u : ι → I | c < clockCount α u ∨ clockCount ω u < c} ⊆
        {u | ζ * N ≤ clockCount α u - N * (α : ℝ)} ∪
        {u | ζ * N ≤ N * (ω : ℝ) - clockCount ω u} := by
    intro u hu
    rcases hu with hu | hu
    · left
      change ζ * N ≤ clockCount α u - N * (α : ℝ)
      change ((α : ℝ) + ζ) * N ≤ c at hleft
      nlinarith
    · right
      change ζ * N ≤ N * (ω : ℝ) - clockCount ω u
      change c ≤ ((ω : ℝ) - ζ) * N at hright
      nlinarith
  calc
    _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

end RobustMatching

#print axioms RobustMatching.independent_bounded_upper_tail
#print axioms RobustMatching.product_bounded_upper_tail
#print axioms RobustMatching.uniform_clock_weighted_upper_tail
#print axioms RobustMatching.uniform_clock_weighted_lower_tail
#print axioms RobustMatching.uniform_clock_batch_upper_tail
#print axioms RobustMatching.paired_batch_range_sq_le
#print axioms RobustMatching.project_away_auxiliary_failure
#print axioms RobustMatching.uniform_clock_cutoff_bracket
