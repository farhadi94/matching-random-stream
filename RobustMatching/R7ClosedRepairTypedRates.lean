import RobustMatching.R7ClosedRepairTypedProfile

/-! Exact realized sender/receiver availability tables. These are proved
from the same endpoint selection and active-gate occupancy used to build
the actual matching, so the mean rates used in concentration have a
concrete graph interface. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RobustMatching.R7ClosedRepair.Typed

variable {G M P I J R U : Type*}

def senderPrimary (s : States G M J R) : Centers G M P I J → Bool
  | .inl g => !(s.active g)
  | _ => true

def senderSecondary (s : States G M J R) : Centers G M P I J → Bool
  | .inl _ => false
  | .inr (.inl m) => s.earlyM m
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr (.inl _))) => false
  | .inr (.inr (.inr (.inr j))) => s.earlyJ j.1

def receiverPrimary (s : States G M J R) : Outsides R M G U → Bool
  | .inl r => s.earlyR r.1
  | .inr (.inl m) => s.earlyM m
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr _)) => true

def receiverSecondary (s : States G M J R) : Outsides R M G U → Bool
  | .inr (.inr (.inl g)) => !(s.active g)
  | _ => true

lemma primary_sender_iff (s : States G M J R) (c : Centers G M P I J) :
    ¬centerOccupied s c ↔ senderPrimary s c = true := by
  rcases c with g | m | p | i | j
  · cases s.active g <;> simp [centerOccupied, senderPrimary]
  all_goals simp [centerOccupied, senderPrimary]

lemma secondary_sender_iff (s : States G M J R) (c : Centers G M P I J) :
    (¬centerSelected s c ∧ ¬centerOccupied s c) ↔ senderSecondary s c = true := by
  rcases c with g | m | p | i | j
  · cases s.active g <;> simp [centerSelected, centerOccupied, senderSecondary]
  · cases s.earlyM m <;> simp [centerSelected, centerOccupied, senderSecondary]
  · simp [centerSelected, centerOccupied, senderSecondary]
  · simp [centerSelected, centerOccupied, senderSecondary]
  · cases s.earlyJ j.1 <;> simp [centerSelected, centerOccupied, senderSecondary]

lemma primary_receiver_iff (s : States G M J R) (x : Outsides R M G U) :
    (¬outsideSelected s x ∧ ¬outsideOccupied s x) ↔ receiverPrimary s x = true := by
  rcases x with r | m | g | u
  · cases s.earlyR r.1 <;> simp [outsideSelected, outsideOccupied, receiverPrimary]
  · cases s.earlyM m <;> simp [outsideSelected, outsideOccupied, receiverPrimary]
  · cases s.active g <;> simp [outsideSelected, outsideOccupied, receiverPrimary]
  · simp [outsideSelected, outsideOccupied, receiverPrimary]

lemma secondary_receiver_iff (s : States G M J R) (x : Outsides R M G U) :
    ¬outsideOccupied s x ↔ receiverSecondary s x = true := by
  rcases x with r | m | g | u
  · simp [outsideOccupied, receiverSecondary]
  · simp [outsideOccupied, receiverSecondary]
  · cases s.active g <;> simp [outsideOccupied, receiverSecondary]
  · simp [outsideOccupied, receiverSecondary]

def senderAt (s : States G M J R)
    (sideO : Outsides R M G U → Bool) (layer : Bool)
    (c : Centers G M P I J) (x : Outsides R M G U) : Bool :=
  if layer = sideO x then senderPrimary s c else senderSecondary s c

def receiverAt (s : States G M J R)
    (sideO : Outsides R M G U → Bool) (layer : Bool)
    (x : Outsides R M G U) : Bool :=
  if layer = sideO x then receiverPrimary s x else receiverSecondary s x

lemma sender_at_iff (s : States G M J R)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (layer : Bool) (c : Centers G M P I J) (x : Outsides R M G U)
    (hcross : sideC c ≠ sideO x) :
    (centerSurvives s sideC layer c ∧ ¬centerOccupied s c) ↔
      senderAt s sideO layer c x = true := by
  by_cases h : layer = sideO x
  · simpa [centerSurvives, senderAt, h, hcross] using primary_sender_iff s c
  · have hc : sideC c = layer := by
      cases h1 : sideC c <;> cases h2 : sideO x <;> cases layer <;> simp_all
    simpa [centerSurvives, senderAt, h, hc] using secondary_sender_iff s c

lemma receiver_at_iff (s : States G M J R)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U) :
    liveReceiver s sideO layer x ↔ receiverAt s sideO layer x = true := by
  by_cases h : layer = sideO x
  · simpa [liveReceiver, outsideSurvives, receiverAt, h] using primary_receiver_iff s x
  · have hn : sideO x ≠ layer := Ne.symm h
    simpa [liveReceiver, outsideSurvives, receiverAt, h, hn] using secondary_receiver_iff s x

def bitMass (b : Bool) : ℝ := if b = true then 1 else 0

/-- The raw matrix is the actual reference incidence times the exact
sender/receiver indicators and the declared availability normalization. -/
theorem raw_support_factorization
    (s : States G M J R)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (hcross : ∀ c x, H c x → sideC c ≠ sideO x)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (scale : Bool → Outsides R M G U → ℝ)
    (layer : Bool) (c : Centers G M P I J) (x : Outsides R M G U) :
    rawSupport s H sideC sideO w scale layer c x =
      if H c x then bitMass (senderAt s sideO layer c x) *
        bitMass (receiverAt s sideO layer x) * w c x / scale layer x else 0 := by
  by_cases hh : H c x
  · have hS := sender_at_iff s sideC sideO layer c x (hcross c x hh)
    have hR := receiver_at_iff s sideO layer x
    have hcond :
        (H c x ∧ centerSurvives s sideC layer c ∧ outsideSurvives s sideO layer x ∧
          ¬centerOccupied s c ∧ ¬outsideOccupied s x) ↔
        (senderAt s sideO layer c x = true ∧ receiverAt s sideO layer x = true) := by
      unfold liveReceiver at hR
      tauto
    unfold rawSupport
    rw [if_pos hh]
    by_cases hs : senderAt s sideO layer c x = true <;>
      by_cases hr : receiverAt s sideO layer x = true <;>
      simp [hcond, hs, hr, bitMass]
  · simp [rawSupport, hh]

end RobustMatching.R7ClosedRepair.Typed
