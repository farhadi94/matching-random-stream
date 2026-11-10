import RandomOrderMatching.Analysis.Repair.Probability.GroupedHoeffding

/-! Actual sender and receiver signals as functions of their original label's
three-category clock. Deterministic vertices have zero fluctuation range. -/
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair.Probability
open RandomOrderMatching.Analysis.Repair.Typed

inductive Signal | zero | one | active | inactive | early | late
  deriving DecidableEq

def signalValue : Signal → Clock → ℝ
  | .zero, _ => 0
  | .one, _ => 1
  | .active, z => bitMass (activeBit z)
  | .inactive, z => bitMass (!(activeBit z))
  | .early, z => bitMass (earlyBit z)
  | .late, z => bitMass (!(earlyBit z))

def signalBase : Signal → ℝ
  | .one => 1
  | _ => 0

def signalRange : Signal → ℝ
  | .zero | .one => 0
  | _ => 1

def signalMean : Signal → ℝ
  | .zero => 0
  | .one => 1
  | .active => alpha
  | .inactive => 1-alpha
  | .early => omega
  | .late => 1-omega

lemma signal_bounds (s : Signal) (z : Clock) : signalValue s z ∈ Set.Icc 0 1 := by
  cases s <;> simp only [signalValue]
  all_goals first | exact bitMass_bounds _ | norm_num

lemma signal_range (s : Signal) (z : Clock) :
    signalValue s z-signalBase s ∈ Set.Icc 0 (signalRange s) := by
  cases s <;> simp only [signalValue, signalBase, signalRange, sub_zero, sub_self]
  all_goals first | exact bitMass_bounds _ | norm_num

@[simp] lemma integral_signal (s : Signal) :
    ∫ z, signalValue s z ∂clockMeasure = signalMean s := by
  cases s <;> simp [signalValue, signalMean]

variable {B G M P I J R U : Type*}

def centerParent (p : Parents B G M J R) (b0 : B) : Centers G M P I J → B
  | .inl g => p.gate g
  | .inr (.inl m) => p.missing m
  | .inr (.inr (.inl _)) => b0
  | .inr (.inr (.inr (.inl _))) => b0
  | .inr (.inr (.inr (.inr j))) => p.internalMissing j.1

def outsideParent (p : Parents B G M J R) (b0 : B) : Outsides R M G U → B
  | .inl r => p.root r.1
  | .inr (.inl m) => p.missing m
  | .inr (.inr (.inl g)) => p.gate g
  | .inr (.inr (.inr _)) => b0

def senderSignal (primary : Bool) : Centers G M P I J → Signal
  | .inl _ => if primary then .inactive else .zero
  | .inr (.inl _) => if primary then .one else .early
  | .inr (.inr (.inl _)) => .one
  | .inr (.inr (.inr (.inl _))) => if primary then .one else .zero
  | .inr (.inr (.inr (.inr _))) => if primary then .one else .early

def receiverSignal (primary : Bool) : Outsides R M G U → Signal
  | .inl _ => if primary then .early else .one
  | .inr (.inl _) => if primary then .early else .one
  | .inr (.inr (.inl _)) => if primary then .zero else .inactive
  | .inr (.inr (.inr _)) => .one

lemma senderSignal_value (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (primary : Bool) (c : Centers G M P I J) :
    signalValue (senderSignal primary c) (z (centerParent p b0 c)) =
      bitMass (if primary then senderPrimary (states p z) c else senderSecondary (states p z) c) := by
  cases primary <;> rcases c with g | m | p' | i | j <;>
    simp [senderSignal,signalValue,centerParent,states,senderPrimary,senderSecondary,bitMass]

lemma receiverSignal_value (p : Parents B G M J R) (b0 : B) (z : B → Clock)
    (primary : Bool) (x : Outsides R M G U) :
    signalValue (receiverSignal primary x) (z (outsideParent p b0 x)) =
      bitMass (if primary then receiverPrimary (states p z) x else receiverSecondary (states p z) x) := by
  cases primary <;> rcases x with r | m | g | u <;>
    simp [receiverSignal,signalValue,outsideParent,states,receiverPrimary,receiverSecondary,bitMass]

lemma senderSignal_mean (primary : Bool) (c : Centers G M P I J) :
    signalMean (senderSignal primary c) =
      if primary then primaryRate alpha c else secondaryRate omega c := by
  cases primary <;> rcases c with g | m | p | i | j <;>
    rfl

lemma receiverSignal_mean (primary : Bool) (x : Outsides R M G U) :
    signalMean (receiverSignal primary x) =
      if primary then primaryCap omega x else secondaryCap alpha x := by
  cases primary <;> rcases x with r | m | g | u <;> rfl

end RandomOrderMatching.Analysis.Repair.Probability
