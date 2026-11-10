import RobustMatching.R7SupportFlowMapBareProfile

noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate
open RobustMatching.R7ClosedRepair.TypedLabeling

section Canonical
variable {B U : Type*} [Fintype B] [Fintype U] [DecidableEq B] [DecidableEq U] {q : ℕ}

def canonicalCenterClass (d : Coordinates B U q) (c : CanonicalCenters d) : CenterClass q :=
  (d.bin (coordinateEquiv d (.inl c)),centerType d c)
def canonicalOutsideClass (d : Coordinates B U q) (x : CanonicalOutsides d) : OutsideClass q :=
  (d.bin (coordinateEquiv d (.inr x)),outsideType d x,d.mask (coordinateEquiv d (.inr x)))

theorem canonical_primary_rate (d : Coordinates B U q) (data : ProfileData q) (c : CanonicalCenters d) :
    (primaryRate data (centerType d c) : ℝ)=
      RobustMatching.R7ClosedRepair.Typed.primaryRate (data.alpha : ℝ) c := by
  rcases c with g | m | p | i | j <;>
    simp [centerType,primaryRate,inactive,RobustMatching.R7ClosedRepair.Typed.primaryRate]

theorem canonical_secondary_rate (d : Coordinates B U q) (data : ProfileData q) (c : CanonicalCenters d) :
    (secondaryRate data (centerType d c) : ℝ)=
      RobustMatching.R7ClosedRepair.Typed.secondaryRate (data.omega : ℝ) c := by
  rcases c with g | m | p | i | j <;>
    simp [centerType,secondaryRate,RobustMatching.R7ClosedRepair.Typed.secondaryRate]

def binWeight (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop) [DecidableRel adj]
    (c : CanonicalCenters d) (x : CanonicalOutsides d) : ℝ :=
  if adj c x then 1/(beta*(max data.cap (1-lower data (canonicalOutsideClass d x).1) : ℚ)) else 0

theorem binWeight_nonneg (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop) [DecidableRel adj]
    (hbeta : 0 < beta) (hcap : 0 < data.cap) (c : CanonicalCenters d) (x : CanonicalOutsides d) :
    0 ≤ binWeight d data beta adj c x := by
  unfold binWeight
  split_ifs
  · have hden : (0 : ℚ) < max data.cap (1-lower data (canonicalOutsideClass d x).1) :=
      hcap.trans_le (le_max_left _ _)
    have hden' : (0 : ℝ) < (max data.cap (1-lower data (canonicalOutsideClass d x).1) : ℚ) := by exact_mod_cast hden
    positivity
  · rfl

theorem bin_primary_load (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop) [DecidableRel adj]
    (x : CanonicalOutsides d) :
    (∑ c, (if adj c x then (1 : ℝ) else 0)*(primaryRate data (centerType d c) : ℝ))/
      (beta*(max data.cap (1-lower data (canonicalOutsideClass d x).1) : ℚ)) =
      RobustMatching.R7ClosedRepair.Typed.primaryLoad (data.alpha : ℝ) (binWeight d data beta adj) x := by
  unfold RobustMatching.R7ClosedRepair.Typed.primaryLoad
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  rw [canonical_primary_rate]
  simp only [binWeight]
  split_ifs <;> ring

theorem bin_secondary_load (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop) [DecidableRel adj]
    (x : CanonicalOutsides d) :
    (∑ c, (if adj c x then (1 : ℝ) else 0)*(secondaryRate data (centerType d c) : ℝ))/
      (beta*(max data.cap (1-lower data (canonicalOutsideClass d x).1) : ℚ)) =
      RobustMatching.R7ClosedRepair.Typed.secondaryLoad (data.omega : ℝ) (binWeight d data beta adj) x := by
  unfold RobustMatching.R7ClosedRepair.Typed.secondaryLoad
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  rw [canonical_secondary_rate]
  simp only [binWeight]
  split_ifs <;> ring

theorem canonical_refund (d : Coordinates B U q) (data : ProfileData q)
    (x : CanonicalOutsides d) (L B : ℝ) (hL : 0 ≤ L) :
    cappedRefund data (outsideType d x) L B =
      min L (RobustMatching.R7ClosedRepair.Typed.primaryCap (data.omega : ℝ) x)+
      min B (RobustMatching.R7ClosedRepair.Typed.secondaryCap (data.alpha : ℝ) x) := by
  rcases x with r | m | g | u <;>
    simp [cappedRefund,outsideType,primaryCap,inactive,
      RobustMatching.R7ClosedRepair.Typed.primaryCap,
      RobustMatching.R7ClosedRepair.Typed.secondaryCap,min_eq_right hL]

theorem typed_primaryLoad_nonneg {G M P I J R U : Type*}
    [Fintype G] [Fintype M] [Fintype P] [Fintype I] [Fintype J]
    [Fintype R] [Fintype U]
    (alpha : ℝ) (w : RobustMatching.R7ClosedRepair.Typed.Centers G M P I J →
      RobustMatching.R7ClosedRepair.Typed.Outsides R M G U → ℝ)
    (ha : alpha ≤ 1) (hw : ∀ c x, 0 ≤ w c x) (x) :
    0 ≤ RobustMatching.R7ClosedRepair.Typed.primaryLoad alpha w x := by
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg _ (hw c x)
  rcases c with g | m | p | i | j <;>
    simp [RobustMatching.R7ClosedRepair.Typed.primaryRate] <;> linarith

theorem canonical_outside_group (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop) [DecidableRel adj]
    (hbeta : 0 < beta) (hcap : 0 < data.cap) (ha : data.alpha ≤ 1)
    (x : CanonicalOutsides d)
    (hmask : d.mask (coordinateEquiv d (.inr x)) = loadMask data (outsideType d x)
      (RobustMatching.R7ClosedRepair.Typed.primaryLoad (data.alpha : ℝ) (binWeight d data beta adj) x)
      (RobustMatching.R7ClosedRepair.Typed.secondaryLoad (data.omega : ℝ) (binWeight d data beta adj) x)) :
    (outsideCredit data (canonicalOutsideClass d x) : ℝ)+
      (∑ c, if adj c x then (edgeCredit data (canonicalCenterClass d c) (canonicalOutsideClass d x) : ℝ) else 0)/beta =
    (min (RobustMatching.R7ClosedRepair.Typed.primaryLoad (data.alpha : ℝ) (binWeight d data beta adj) x)
        (RobustMatching.R7ClosedRepair.Typed.primaryCap (data.omega : ℝ) x)+
      min (RobustMatching.R7ClosedRepair.Typed.secondaryLoad (data.omega : ℝ) (binWeight d data beta adj) x)
        (RobustMatching.R7ClosedRepair.Typed.secondaryCap (data.alpha : ℝ) x))/2 := by
  have hh := outside_affine_group data (canonicalOutsideClass d x).1 (outsideType d x)
    (d.mask (coordinateEquiv d (.inr x))) (canonicalCenterClass d)
    (fun c => if adj c x then (1 : ℝ) else 0) beta
  simp only [ite_mul,one_mul,zero_mul] at hh
  have hx : ((canonicalOutsideClass d x).1,outsideType d x,d.mask (coordinateEquiv d (.inr x))) =
      canonicalOutsideClass d x := rfl
  rw [hx] at hh
  rw [hh]
  change affineRefund data (outsideType d x) (d.mask (coordinateEquiv d (.inr x))) _ _/2 = _
  have hL := bin_primary_load d data beta adj x
  have hB := bin_secondary_load d data beta adj x
  simp only [ite_mul,one_mul,zero_mul] at hL hB
  change affineRefund data (outsideType d x) (d.mask (coordinateEquiv d (.inr x)))
    ((∑ c, if adj c x then (primaryRate data (centerType d c) : ℝ) else 0)/_)
    ((∑ c, if adj c x then (secondaryRate data (centerType d c) : ℝ) else 0)/_)/2 = _
  rw [hL,hB,hmask,loadMask_refund]
  rw [canonical_refund]
  exact typed_primaryLoad_nonneg _ _ (by exact_mod_cast ha) (binWeight_nonneg d data beta adj hbeta hcap) x

end Canonical
end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.canonical_outside_group
