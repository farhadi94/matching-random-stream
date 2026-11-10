import RobustMatching.R7SupportFlowMapTypedProfile

noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate
open RobustMatching.R7ClosedRepair.TypedLabeling

theorem typed_profile_mono {G M P I J R U : Type*}
    [Fintype G] [Fintype M] [Fintype P] [Fintype I] [Fintype J]
    [Fintype R] [Fintype U]
    (alpha omega : ℝ)
    (w w' : RobustMatching.R7ClosedRepair.Typed.Centers G M P I J →
      RobustMatching.R7ClosedRepair.Typed.Outsides R M G U → ℝ)
    (ha : alpha ≤ 1) (ho : 0 ≤ omega) (hw : ∀ c x, w c x ≤ w' c x) :
    RobustMatching.R7ClosedRepair.Typed.profile alpha omega w ≤
      RobustMatching.R7ClosedRepair.Typed.profile alpha omega w' := by
  have hP (x) : RobustMatching.R7ClosedRepair.Typed.primaryLoad alpha w x ≤
      RobustMatching.R7ClosedRepair.Typed.primaryLoad alpha w' x := by
    apply Finset.sum_le_sum
    intro c _
    apply mul_le_mul_of_nonneg_left (hw c x)
    rcases c with g | m | p | i | j <;>
      simp [RobustMatching.R7ClosedRepair.Typed.primaryRate] <;> linarith
  have hS (x) : RobustMatching.R7ClosedRepair.Typed.secondaryLoad omega w x ≤
      RobustMatching.R7ClosedRepair.Typed.secondaryLoad omega w' x := by
    apply Finset.sum_le_sum
    intro c _
    apply mul_le_mul_of_nonneg_left (hw c x)
    rcases c with g | m | p | i | j <;>
      simp [RobustMatching.R7ClosedRepair.Typed.secondaryRate,ho]
  have hO : RobustMatching.R7ClosedRepair.Typed.outsideProfile alpha omega w ≤
      RobustMatching.R7ClosedRepair.Typed.outsideProfile alpha omega w' := by
    apply Finset.sum_le_sum
    intro x _
    exact add_le_add (min_le_min (hP x) le_rfl) (min_le_min (hS x) le_rfl)
  unfold RobustMatching.R7ClosedRepair.Typed.profile
  linarith

theorem binWeight_le_actual {B U : Type*} [Fintype B] [Fintype U]
    [DecidableEq B] [DecidableEq U] {q}
    (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop) [DecidableRel adj]
    (a : CanonicalOutsides d → ℝ) (hbeta : 0 < beta) (hcap : 0 < data.cap)
    (hbin : ∀ x, (lower data (canonicalOutsideClass d x).1 : ℝ) ≤ a x)
    (c : CanonicalCenters d) (x : CanonicalOutsides d) :
    binWeight d data beta adj c x ≤
      (if adj c x then 1/(beta*max (data.cap : ℝ) (1-a x)) else 0) := by
  unfold binWeight
  split_ifs
  · have hc : (0 : ℝ) < data.cap := by exact_mod_cast hcap
    simpa only [Rat.cast_max,Rat.cast_sub,Rat.cast_one] using
      RobustMatching.R7SupportFlow.bin_capped_weight_lower hbeta hc (hbin x)
  · rfl

end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.typed_profile_mono
#print axioms RobustMatching.R7SupportFlowMap.binWeight_le_actual
