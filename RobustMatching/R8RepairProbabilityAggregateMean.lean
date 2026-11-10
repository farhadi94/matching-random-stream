import RobustMatching.R8RepairProbabilityAggregateMixed

/-! Exact expectation and bounded coefficients for the actual mixed repair.
The only weight assumptions are nonnegativity and sender row capacity. -/
noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
open Classical MeasureTheory
open scoped BigOperators
namespace RobustMatching.R8RepairProbability
open R7ClosedRepair R7ClosedRepair.Typed

variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]

lemma signalMean_bounds (s : Signal) : signalMean s ∈ Set.Icc (0 : ℝ) 1 := by
  cases s <;> norm_num [signalMean, alpha, omega]

lemma aggregateCap_eq_mean (primary : Bool) (x : Outsides R M G U) :
    aggregateCap primary x = signalMean (receiverSignal primary x) := by
  rw [receiverSignal_mean]
  rfl

lemma aggregateLoad_eq_mean (w : Centers G M P I J → Outsides R M G U → ℝ)
    (primary : Bool) (x : Outsides R M G U) :
    aggregateLoad w primary x = ∑ c, w c x * signalMean (senderSignal primary c) := by
  simp_rw [senderSignal_mean]
  cases primary <;> simp [aggregateLoad, primaryLoad, secondaryLoad, mul_comm]

lemma aggregateLoad_nonneg (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (primary : Bool) (x : Outsides R M G U) :
    0 ≤ aggregateLoad w primary x := by
  rw [aggregateLoad_eq_mean]
  exact Finset.sum_nonneg fun c _ => mul_nonneg (hw c x) (signalMean_bounds _).1

lemma receiverCoefficient_bounds
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (primary : Bool) (x : Outsides R M G U) :
    receiverCoefficient w primary x ∈ Set.Icc (0 : ℝ) 1 := by
  have hc := (signalMean_bounds (receiverSignal primary x)).1
  rw [← aggregateCap_eq_mean] at hc
  have hl := aggregateLoad_nonneg w hw primary x
  by_cases hz : aggregateCap primary x = 0
  · simp [receiverCoefficient, hz]
  · have hp := lt_of_le_of_ne hc (Ne.symm hz)
    exact ⟨div_nonneg (le_min hl hc) hc,
      (div_le_one hp).mpr (min_le_right _ _)⟩

lemma receiverCoefficient_mean
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (primary : Bool) (x : Outsides R M G U) :
    receiverCoefficient w primary x * signalMean (receiverSignal primary x) =
      min (aggregateLoad w primary x) (aggregateCap primary x) := by
  rw [← aggregateCap_eq_mean]
  by_cases hz : aggregateCap primary x = 0
  · simp [receiverCoefficient, hz, min_eq_right (aggregateLoad_nonneg w hw primary x)]
  · exact div_mul_cancel₀ _ hz

lemma lowSenderCoefficient_bounds
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (hrow : ∀ c, ∑ x, w c x ≤ 1)
    (c : Centers G M P I J) : lowSenderCoefficient w c ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun x _ => by
      split_ifs
      · exact hw c x
      · exact le_rfl
  · refine (Finset.sum_le_sum (fun x _ => ?_)).trans (hrow c)
    split_ifs
    · exact le_rfl
    · exact hw c x

lemma mixedCoefficient_bounds
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (hrow : ∀ c, ∑ x, w c x ≤ 1)
    (i : MixedIndex G M P I J R U) : mixedCoefficient w i ∈ Set.Icc (0 : ℝ) 1 := by
  rcases i with ⟨primary,x⟩ | ⟨primary,c⟩
  · dsimp only [mixedCoefficient]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact receiverCoefficient_bounds w hw primary x
  · exact lowSenderCoefficient_bounds w hw hrow c

lemma low_load_min
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (primary : Bool) (x : Outsides R M G U)
    (hx : lowUnmatched w x) :
    min (aggregateLoad w primary x) (aggregateCap primary x) = aggregateLoad w primary x := by
  rcases x with r | m | g | u
  all_goals simp only [lowUnmatched] at hx
  all_goals try contradiction
  have hc : aggregateCap primary (.inr (.inr (.inr u)) : Outsides R M G U) = 1 := by
    cases primary <;> rfl
  rw [hc, min_eq_left]
  rw [aggregateLoad_eq_mean]
  exact (Finset.sum_le_sum (fun c _ => mul_le_of_le_one_right (hw c _) (signalMean_bounds _).2)).trans hx

/-- The signal expectation is exactly the deterministic outside profile,
including every low unmatched leaf. -/
theorem mixedExpectation_eq_outsideProfile
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) :
    signalExpectation mixedSignal (mixedCoefficient w) = outsideProfile alpha omega w := by
  have hlow :
      (∑ primary : Bool, ∑ c, lowSenderCoefficient w c * signalMean (senderSignal primary c)) =
        ∑ x, ∑ primary : Bool, if lowUnmatched w x then aggregateLoad w primary x else 0 := by
    simp only [lowSenderCoefficient, Finset.sum_mul]
    conv_lhs => arg 2; ext primary; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro primary _
    by_cases hh : lowUnmatched w x
    · simp only [hh, if_true, aggregateLoad_eq_mean]
    · simp only [hh, if_false, zero_mul, Finset.sum_const_zero]
  unfold signalExpectation
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, mixedSignal, mixedCoefficient]
  rw [hlow]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  unfold outsideProfile
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  have ht (primary : Bool) :
      (if lowUnmatched w x then 0 else receiverCoefficient w primary x) *
        signalMean (receiverSignal primary x) +
        (if lowUnmatched w x then aggregateLoad w primary x else 0) =
      min (aggregateLoad w primary x) (aggregateCap primary x) := by
    by_cases hh : lowUnmatched w x
    · simp [hh, low_load_min w hw primary x hh]
    · simp [hh, receiverCoefficient_mean w hw primary x]
  simp_rw [ht]
  simp only [Fintype.sum_bool, aggregateLoad, aggregateCap, Bool.false_eq_true,
    if_false, if_true]

end RobustMatching.R8RepairProbability
