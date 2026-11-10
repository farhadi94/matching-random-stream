import RandomOrderMatching.Analysis.Profile.SupportIdentity

noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Certificates.DegreeProfile
open RandomOrderMatching.Analysis.Repair.Labeling

variable {B U E : Type*} [Fintype B] [Fintype U] [Fintype E]
  [DecidableEq B] [DecidableEq U] {q : ℕ}

theorem coordinate_outside_credit (d : Coordinates B U q) (data : ProfileData q) :
    (∑ v, vertexOutsideCredit data (vertexColumn d v)) =
      ∑ x : CanonicalOutsides d, (outsideCredit data (canonicalOutsideClass d x) : ℝ) := by
  rw [←(coordinateEquiv d).sum_comp]
  simp only [coordinate_vertex_column,Fintype.sum_sum_type,canonicalColumn,
    vertexOutsideCredit,Finset.sum_const_zero,zero_add,canonicalOutsideClass]

theorem rawProfile_eq_bin_profile
    (d : Coordinates B U q) (ref : E → Column q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop)
    (hbeta : 0 < beta) (hcap : 0 < data.cap) (ha : data.alpha ≤ 1)
    (hreference : (∑ e, (coeffLe data .phase (ref e) : ℝ)) =
      ∑ c : CanonicalCenters d, ∑ x : CanonicalOutsides d,
        if adj c x then (edgeCredit data (canonicalCenterClass d c) (canonicalOutsideClass d x) : ℝ) else 0)
    (hmask : ∀ x : CanonicalOutsides d, d.mask (coordinateEquiv d (.inr x)) =
      loadMask data (outsideType d x)
        (RandomOrderMatching.Analysis.Repair.Typed.primaryLoad (data.alpha : ℝ) (binWeight d data beta adj) x)
        (RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad (data.omega : ℝ) (binWeight d data beta adj) x)) :
    rawProfile d ref data beta =
      RandomOrderMatching.Analysis.Repair.Typed.profile (data.alpha : ℝ) (data.omega : ℝ)
        (binWeight d data beta adj) := by
  have hgroup : (∑ x : CanonicalOutsides d,
      (outsideCredit data (canonicalOutsideClass d x) : ℝ))+
      (∑ c : CanonicalCenters d, ∑ x : CanonicalOutsides d,
        if adj c x then (edgeCredit data (canonicalCenterClass d c) (canonicalOutsideClass d x) : ℝ) else 0)/beta =
      RandomOrderMatching.Analysis.Repair.Typed.outsideProfile (data.alpha : ℝ) (data.omega : ℝ)
        (binWeight d data beta adj)/2 := by
    rw [Finset.sum_comm,Finset.sum_div,←Finset.sum_add_distrib]
    simp_rw [canonical_outside_group d data beta adj hbeta hcap ha _ (hmask _)]
    rw [←Finset.sum_div]
    rfl
  rw [rawProfile_split,coordinate_outside_credit,hreference]
  rw [add_assoc,hgroup]
  simp only [kindCount_eq_fiber_card]
  unfold RandomOrderMatching.Analysis.Repair.Typed.profile
  ring

end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.rawProfile_eq_bin_profile
