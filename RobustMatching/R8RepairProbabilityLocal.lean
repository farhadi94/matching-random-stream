import RobustMatching.R8RepairProbabilitySignalTails

/-! Actual local repair events. Upper rows are dominated by receiver-only
sums; lower columns follow from sender-only sums on every live outcome.
Thus shared own-parent clocks require no conditional-independence claim. -/
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RobustMatching.R8RepairProbability
open R7ClosedRepair R7ClosedRepair.Typed

variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]

def senderSignalAt (sideO : Outsides R M G U → Bool) (layer : Bool)
    (x : Outsides R M G U) : Centers G M P I J → Signal :=
  senderSignal (decide (layer = sideO x))

def receiverSignalAt (sideO : Outsides R M G U → Bool) (layer : Bool)
    (x : Outsides R M G U) : Signal :=
  receiverSignal (decide (layer = sideO x)) x

lemma senderSignalAt_value (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (sideO : Outsides R M G U → Bool) (layer : Bool)
    (c : Centers G M P I J) (x : Outsides R M G U) :
    signalValue (senderSignalAt sideO layer x c) (z (centerParent p b0 c)) =
      bitMass (senderAt (states p z) sideO layer c x) := by
  unfold senderSignalAt
  rw [senderSignal_value]
  by_cases h : layer=sideO x <;> simp [h,senderAt]

lemma receiverSignalAt_value (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U) :
    signalValue (receiverSignalAt sideO layer x) (z (outsideParent p b0 x)) =
      bitMass (receiverAt (states p z) sideO layer x) := by
  unfold receiverSignalAt
  rw [receiverSignal_value]
  by_cases h : layer=sideO x <;> simp [h,receiverAt]

lemma receiverSignalAt_mean (sideO : Outsides R M G U → Bool) (layer : Bool)
    (x : Outsides R M G U) :
    signalMean (receiverSignalAt sideO layer x) = capacity alpha omega sideO layer x := by
  unfold receiverSignalAt
  rw [receiverSignal_mean]
  by_cases h : layer=sideO x <;> simp [h,capacity]

lemma senderExpectation_eq (w : Centers G M P I J → Outsides R M G U → ℝ)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U) :
    signalExpectation (senderSignalAt sideO layer x) (fun c => w c x) =
      meanLoad alpha omega w sideO layer x := by
  unfold signalExpectation senderSignalAt
  simp_rw [senderSignal_mean]
  by_cases h : layer=sideO x <;>
    simp [h,meanLoad,primaryLoad,secondaryLoad,mul_comm]

lemma parameters : alpha<1 ∧ 0<omega := by norm_num [alpha,omega]

lemma receiverExpectation_le (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x,0≤w c x) (sideO : Outsides R M G U → Bool) (layer : Bool)
    (c : Centers G M P I J) :
    signalExpectation (receiverSignalAt sideO layer)
      (fun x => w c x/normalizer alpha omega sideO layer x) ≤ ∑ x,w c x := by
  apply Finset.sum_le_sum
  intro x _
  rw [receiverSignalAt_mean]
  dsimp only [normalizer]
  split_ifs with h
  · simp [h,hw c x]
  · have hc := capacity_nonneg alpha omega parameters.1 parameters.2 sideO layer x
    have hp := lt_of_le_of_ne hc (Ne.symm h)
    exact le_of_eq (div_mul_cancel₀ _ (ne_of_gt hp))

lemma row_dominated
    (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (hcross : ∀ c x,H c x→sideC c≠sideO x)
    (w : Centers G M P I J → Outsides R M G U → ℝ) (hw : ∀c x,0≤w c x)
    (layer : Bool) (c : Centers G M P I J) :
    rowLoad (rawSupport (states p z) H sideC sideO w (normalizer alpha omega sideO) layer) c ≤
      signalSum (outsideParent p b0) (receiverSignalAt sideO layer)
        (fun x => w c x/normalizer alpha omega sideO layer x) z := by
  apply Finset.sum_le_sum
  intro x _
  rw [raw_support_factorization _ _ _ _ hcross, receiverSignalAt_value]
  have hn := normalizer_pos alpha omega parameters.1 parameters.2 sideO layer x
  have hr := bitMass_bounds (receiverAt (states p z) sideO layer x)
  split_ifs with hH
  · have hs := bitMass_bounds (senderAt (states p z) sideO layer c x)
    have hh : bitMass (senderAt (states p z) sideO layer c x)*
        bitMass (receiverAt (states p z) sideO layer x)*w c x ≤
        bitMass (receiverAt (states p z) sideO layer x)*w c x := by
      nlinarith [mul_nonneg hr.1 (hw c x), hs.2]
    convert div_le_div_of_nonneg_right hh (le_of_lt hn) using 1 <;> ring
  · exact mul_nonneg (div_nonneg (hw c x) (le_of_lt hn)) hr.1

lemma live_column_eq
    (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (hcross : ∀ c x,H c x→sideC c≠sideO x)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hsupport : ∀ c x,¬H c x→w c x=0)
    (layer : Bool) (x : Outsides R M G U)
    (hlive : liveReceiver (states p z) sideO layer x) :
    colLoad (rawSupport (states p z) H sideC sideO w (normalizer alpha omega sideO) layer) x =
      signalSum (centerParent p b0) (senderSignalAt sideO layer x) (fun c => w c x) z /
        capacity alpha omega sideO layer x := by
  have hr := (receiver_at_iff (states p z) sideO layer x).mp hlive
  have hp := live_capacity_pos (states p z) alpha omega parameters.1 parameters.2 sideO layer x hlive
  unfold colLoad signalSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  rw [raw_support_factorization _ _ _ _ hcross, senderSignalAt_value]
  by_cases hh : H c x
  · simp [hh,hr,bitMass,normalizer,ne_of_gt hp,mul_comm]
  · simp [hh,hsupport c x hh]

/-- Upper-load failure for an actual clipped-repair row. -/
theorem actual_row_tail
    (p : Parents B G M J R) (b0 : B)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (hcross : ∀ c x,H c x→sideC c≠sideO x)
    (w : Centers G M P I J → Outsides R M G U → ℝ) (hw : ∀c x,0≤w c x)
    (hrow : ∀c,∑x,w c x≤1) (layer : Bool) (c : Centers G M P I J)
    {t : ℝ} (ht : 0≤t) :
    (experiment (B:=B)).real {z | 1+t < rowLoad
      (rawSupport (states p z) H sideC sideO w (normalizer alpha omega sideO) layer) c} ≤
      Real.exp (-2*t^2 / ∑ b, (blockRange (outsideParent p b0)
        (signalRanges (receiverSignalAt sideO layer)
          (fun x => w c x/normalizer alpha omega sideO layer x)) b)^2) := by
  have ha : ∀x,0≤w c x/normalizer alpha omega sideO layer x := fun x =>
    div_nonneg (hw c x) (le_of_lt (normalizer_pos alpha omega parameters.1 parameters.2 sideO layer x))
  refine (measureReal_mono ?_).trans (signal_upper_tail (outsideParent p b0)
    (receiverSignalAt sideO layer) _ ha ht)
  intro z hz
  change 1+t < rowLoad (rawSupport (states p z) H sideC sideO w
    (normalizer alpha omega sideO) layer) c at hz
  have hr := row_dominated p b0 z H sideC sideO hcross w hw layer c
  have hm := (receiverExpectation_le w hw sideO layer c).trans (hrow c)
  change t≤signalSum _ _ _ z-signalExpectation _ _
  linarith

/-- Lower-load failure is measured on the actual live-receiver event.
The sender-only concentration estimate is unconditional, even when its own
parent appears among those senders. -/
theorem actual_column_tail
    (p : Parents B G M J R) (b0 : B)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (hcross : ∀ c x,H c x→sideC c≠sideO x)
    (w : Centers G M P I J → Outsides R M G U → ℝ) (hw : ∀c x,0≤w c x)
    (hsupport : ∀ c x,¬H c x→w c x=0)
    (layer : Bool) (x : Outsides R M G U) {t : ℝ} (ht : 0≤t) :
    (experiment (B:=B)).real {z | liveReceiver (states p z) sideO layer x ∧
      colLoad (rawSupport (states p z) H sideC sideO w (normalizer alpha omega sideO) layer) x <
        (meanLoad alpha omega w sideO layer x-t)/capacity alpha omega sideO layer x} ≤
      Real.exp (-2*t^2 / ∑ b, (blockRange (centerParent p b0)
        (signalRanges (senderSignalAt sideO layer x) (fun c => w c x)) b)^2) := by
  refine (measureReal_mono ?_).trans (signal_lower_tail (centerParent p b0)
    (senderSignalAt sideO layer x) _ (fun c => hw c x) ht)
  rintro z ⟨hlive,hz⟩
  rw [live_column_eq p b0 z H sideC sideO hcross w hsupport layer x hlive] at hz
  have hp := live_capacity_pos (states p z) alpha omega parameters.1 parameters.2 sideO layer x hlive
  have hh := (div_lt_div_iff_of_pos_right hp).mp hz
  change t≤signalExpectation _ _-signalSum _ _ _ z
  rw [senderExpectation_eq]
  linarith

end RobustMatching.R8RepairProbability
