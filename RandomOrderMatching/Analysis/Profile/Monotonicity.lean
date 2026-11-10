import RandomOrderMatching.Analysis.Profile.SupportIdentity

noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Certificates.DegreeProfile
open RandomOrderMatching.Analysis.Repair.Labeling

theorem typed_profile_mono {G M P I J R U : Type*}
    [Fintype G] [Fintype M] [Fintype P] [Fintype I] [Fintype J]
    [Fintype R] [Fintype U]
    (alpha omega : ℝ)
    (w w' : RandomOrderMatching.Analysis.Repair.Typed.Centers G M P I J →
      RandomOrderMatching.Analysis.Repair.Typed.Outsides R M G U → ℝ)
    (ha : alpha ≤ 1) (ho : 0 ≤ omega) (hw : ∀ c x, w c x ≤ w' c x) :
    RandomOrderMatching.Analysis.Repair.Typed.profile alpha omega w ≤
      RandomOrderMatching.Analysis.Repair.Typed.profile alpha omega w' := by
  have hP (x) : RandomOrderMatching.Analysis.Repair.Typed.primaryLoad alpha w x ≤
      RandomOrderMatching.Analysis.Repair.Typed.primaryLoad alpha w' x := by
    apply Finset.sum_le_sum
    intro c _
    apply mul_le_mul_of_nonneg_left (hw c x)
    rcases c with g | m | p | i | j <;>
      simp [RandomOrderMatching.Analysis.Repair.Typed.primaryRate] <;> linarith
  have hS (x) : RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad omega w x ≤
      RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad omega w' x := by
    apply Finset.sum_le_sum
    intro c _
    apply mul_le_mul_of_nonneg_left (hw c x)
    rcases c with g | m | p | i | j <;>
      simp [RandomOrderMatching.Analysis.Repair.Typed.secondaryRate,ho]
  have hO : RandomOrderMatching.Analysis.Repair.Typed.outsideProfile alpha omega w ≤
      RandomOrderMatching.Analysis.Repair.Typed.outsideProfile alpha omega w' := by
    apply Finset.sum_le_sum
    intro x _
    exact add_le_add (min_le_min (hP x) le_rfl) (min_le_min (hS x) le_rfl)
  unfold RandomOrderMatching.Analysis.Repair.Typed.profile
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
      RandomOrderMatching.Analysis.Support.bin_capped_weight_lower hbeta hc (hbin x)
  · rfl

end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.typed_profile_mono
#print axioms RandomOrderMatching.Analysis.Profile.binWeight_le_actual
