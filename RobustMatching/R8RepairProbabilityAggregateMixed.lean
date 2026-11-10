import RobustMatching.R8RepairProbabilityLocal
import RobustMatching.R8RepairProbabilityBudgets

/-! Exact original-parent decomposition of the actual mixed repair value.
Low unmatched leaves are collected by sender; no independent-copy model or
assumed expectation is used. -/
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

def aggregateLoad (w : Centers G M P I J → Outsides R M G U → ℝ)
    (primary : Bool) (x : Outsides R M G U) : ℝ :=
  if primary then primaryLoad alpha w x else secondaryLoad omega w x

def aggregateCap (primary : Bool) (x : Outsides R M G U) : ℝ :=
  if primary then primaryCap omega x else secondaryCap alpha x

def receiverCoefficient (w : Centers G M P I J → Outsides R M G U → ℝ)
    (primary : Bool) (x : Outsides R M G U) : ℝ :=
  min (aggregateLoad w primary x) (aggregateCap primary x) / aggregateCap primary x

def lowSenderCoefficient (w : Centers G M P I J → Outsides R M G U → ℝ)
    (c : Centers G M P I J) : ℝ :=
  ∑ x, if lowUnmatched w x then w c x else 0

abbrev MixedIndex (G M P I J R U : Type*) :=
  (Bool × Outsides R M G U) ⊕ (Bool × Centers G M P I J)

def mixedParent (p : Parents B G M J R) (b0 : B) : MixedIndex G M P I J R U → B
  | .inl bx => outsideParent p b0 bx.2
  | .inr bc => centerParent p b0 bc.2

def mixedSignal : MixedIndex G M P I J R U → Signal
  | .inl bx => receiverSignal bx.1 bx.2
  | .inr bc => senderSignal bc.1 bc.2

def mixedCoefficient (w : Centers G M P I J → Outsides R M G U → ℝ) :
    MixedIndex G M P I J R U → ℝ
  | .inl bx => if lowUnmatched w bx.2 then 0 else receiverCoefficient w bx.1 bx.2
  | .inr bc => lowSenderCoefficient w bc.2

lemma availability_signal
    (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U) :
    availabilityValue (states p z) alpha omega w sideO layer x =
      receiverCoefficient w (decide (layer = sideO x)) x *
        signalValue (receiverSignalAt sideO layer x) (z (outsideParent p b0 x)) := by
  rw [receiverSignalAt_value]
  have hr := receiver_at_iff (states p z) sideO layer x
  unfold availabilityValue receiverTarget receiverCoefficient aggregateLoad aggregateCap
  rw [hr]
  by_cases hl : layer = sideO x <;>
    by_cases hb : receiverAt (states p z) sideO layer x = true <;>
    simp [hl, meanLoad, capacity, bitMass, hr, hb]

lemma sum_availability_signal
    (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (sideO : Outsides R M G U → Bool) (x : Outsides R M G U) :
    (∑ layer : Bool, availabilityValue (states p z) alpha omega w sideO layer x) =
      ∑ primary : Bool, receiverCoefficient w primary x *
        signalValue (receiverSignal primary x) (z (outsideParent p b0 x)) := by
  simp_rw [availability_signal p b0 z]
  cases hs : sideO x <;> simp [Fintype.sum_bool, hs, receiverSignalAt, add_comm]

lemma low_unmatched_live (p : Parents B G M J R) (z : B → Clock)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U)
    (hx : lowUnmatched w x) : liveReceiver (states p z) sideO layer x := by
  rcases x with r | m | g | u
  all_goals simp only [lowUnmatched] at hx
  all_goals simp_all [liveReceiver, outsideSurvives, outsideSelected, outsideOccupied]

lemma low_unmatched_capacity
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U)
    (hx : lowUnmatched w x) : capacity alpha omega sideO layer x = 1 := by
  rcases x with r | m | g | u
  all_goals simp only [lowUnmatched] at hx
  all_goals simp_all [capacity, primaryCap, secondaryCap]

lemma sum_low_raw_signal
    (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (hcross : ∀ c x, H c x → sideC c ≠ sideO x)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hsupport : ∀ c x, ¬H c x → w c x = 0)
    (x : Outsides R M G U) (hx : lowUnmatched w x) :
    (∑ layer : Bool, colLoad (rawSupport (states p z) H sideC sideO w
      (normalizer alpha omega sideO) layer) x) =
      ∑ primary : Bool, ∑ c, w c x *
        signalValue (senderSignal primary c) (z (centerParent p b0 c)) := by
  have he (layer : Bool) := live_column_eq p b0 z H sideC sideO hcross w hsupport
    layer x (low_unmatched_live p z w sideO layer x hx)
  simp_rw [he, low_unmatched_capacity w sideO _ x hx, div_one]
  simp only [Fintype.sum_bool]
  cases hs : sideO x <;> simp only [senderSignalAt, hs, Bool.false_eq_true,
    Bool.true_eq_false, decide_true, decide_false]
  · exact add_comm _ _
  · rfl

/-- Every realized mixed value is a sum of categorical signals of original
parents. Arbitrarily many low unmatched receivers have been collected into
one coefficient per sender. -/
theorem mixedValue_eq_signalSum
    (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (hcross : ∀ c x, H c x → sideC c ≠ sideO x)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hsupport : ∀ c x, ¬H c x → w c x = 0) :
    (∑ layer : Bool, ∑ x, mixedValue (states p z) alpha omega H sideC sideO w layer x) =
      signalSum (mixedParent p b0) mixedSignal (mixedCoefficient w) z := by
  have hx (x : Outsides R M G U) :
      (∑ layer : Bool, mixedValue (states p z) alpha omega H sideC sideO w layer x) =
        (∑ primary : Bool, (if lowUnmatched w x then 0 else receiverCoefficient w primary x) *
          signalValue (receiverSignal primary x) (z (outsideParent p b0 x))) +
        (∑ primary : Bool, ∑ c, (if lowUnmatched w x then w c x else 0) *
          signalValue (senderSignal primary c) (z (centerParent p b0 c))) := by
    by_cases hh : lowUnmatched w x
    · simpa only [mixedValue, hh, if_true, zero_mul, Finset.sum_const_zero, zero_add] using
        sum_low_raw_signal p b0 z H sideC sideO hcross w hsupport x hh
    · simpa only [mixedValue, hh, if_false, zero_mul, Finset.sum_const_zero, add_zero] using
        sum_availability_signal p b0 z w sideO x
  rw [Finset.sum_comm]
  simp_rw [hx]
  rw [Finset.sum_add_distrib]
  unfold signalSum
  conv_rhs => rw [Fintype.sum_sum_type]
  congr 1
  · rw [Finset.sum_comm]
    simp only [Fintype.sum_prod_type, mixedParent, mixedSignal, mixedCoefficient]
  · rw [Finset.sum_comm]
    simp only [Fintype.sum_prod_type, mixedParent, mixedSignal, mixedCoefficient]
    apply Finset.sum_congr rfl
    intro primary _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    simp only [lowSenderCoefficient, Finset.sum_mul]

end RobustMatching.R8RepairProbability
