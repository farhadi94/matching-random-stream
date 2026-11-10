import RandomOrderMatching.Analysis.Profile.SupportIdentity

noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Certificates.DegreeProfile
open RandomOrderMatching.Analysis.Repair.Labeling

local instance universalDecidableRel {A C : Type*} (r : A → C → Prop) : DecidableRel r :=
  fun _ _ => Classical.propDecidable _

variable {B U : Type*} [Fintype B] [Fintype U] [DecidableEq B] [DecidableEq U] {q : ℕ}

abbrev minimumMaskCoordinates (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop) : Coordinates B U q :=
  { d with mask := fun v => match (coordinateEquiv d).symm v with
      | .inl _ => 0
      | .inr x => loadMask data (outsideType d x)
          (RandomOrderMatching.Analysis.Repair.Typed.primaryLoad (data.alpha : ℝ) (binWeight d data beta adj) x)
          (RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad (data.omega : ℝ) (binWeight d data beta adj) x) }

theorem minimumMask_coordinate (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop) (v : CanonicalVertex d) :
    coordinateEquiv (minimumMaskCoordinates d data beta adj) v=coordinateEquiv d v := by
  rcases v with c | x
  · rcases c with g | m | p | i | j <;> rfl
  · rcases x with r | m | g | u <;> rfl

theorem minimumMask_outside_type (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop) (x : CanonicalOutsides d) :
    outsideType (minimumMaskCoordinates d data beta adj) x=outsideType d x := by
  rcases x with r | m | g | u <;> rfl

theorem minimumMask_identity (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop)
    (x : CanonicalOutsides d) :
    (minimumMaskCoordinates d data beta adj).mask
      (coordinateEquiv (minimumMaskCoordinates d data beta adj) (.inr x)) =
      loadMask data (outsideType d x)
        (RandomOrderMatching.Analysis.Repair.Typed.primaryLoad (data.alpha : ℝ)
          (binWeight d data beta adj) x)
        (RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad (data.omega : ℝ)
          (binWeight d data beta adj) x) := by
  rw [minimumMask_coordinate]
  change (match (coordinateEquiv d).symm (coordinateEquiv d (.inr x)) with
      | .inl _ => 0
      | .inr x => loadMask data (outsideType d x)
          (RandomOrderMatching.Analysis.Repair.Typed.primaryLoad (data.alpha : ℝ) (binWeight d data beta adj) x)
          (RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad (data.omega : ℝ) (binWeight d data beta adj) x)) = _
  rw [Equiv.symm_apply_apply]

theorem minimumMask_allowed (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop)
    (hlow : ∀ x : CanonicalOutsides d, outsideType d x=.O →
      upper data (canonicalOutsideClass d x).1 ≤ 1/2 →
      RandomOrderMatching.Analysis.Repair.Typed.primaryLoad (data.alpha : ℝ) (binWeight d data beta adj) x ≤ 1 ∧
      RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad (data.omega : ℝ) (binWeight d data beta adj) x ≤ 1)
    (v : Vertex B U) :
    columnAllowed data (vertexColumn (minimumMaskCoordinates d data beta adj) v) := by
  let d' := minimumMaskCoordinates d data beta adj
  obtain ⟨z,rfl⟩ := (coordinateEquiv d').surjective v
  rw [coordinate_vertex_column]
  cases z with
  | inl c => trivial
  | inr x =>
    change outsideAllowed data (_,outsideType d' x,d'.mask (coordinateEquiv d' (.inr x)))
    rw [minimumMask_identity]
    rw [minimumMask_coordinate,minimumMask_outside_type]
    exact loadMask_allowed data _ _ _ _ (hlow x)

theorem binWeight_low_column (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop)
    (hbeta : 0 < beta) (hcap : 0 < data.cap)
    (x : CanonicalOutsides d)
    (hcount : (∑ c : CanonicalCenters d, if adj c x then (1 : ℝ) else 0) ≤
      beta*(upper data (canonicalOutsideClass d x).1 : ℝ))
    (hbins : lower data (canonicalOutsideClass d x).1 ≤ upper data (canonicalOutsideClass d x).1)
    (hlow : upper data (canonicalOutsideClass d x).1 ≤ 1/2) :
    (∑ c, binWeight d data beta adj c x) ≤ 1 := by
  let den : ℝ := (max data.cap (1-lower data (canonicalOutsideClass d x).1) : ℚ)
  have hden : 0 < den := by
    have hh : (0 : ℚ) < max data.cap (1-lower data (canonicalOutsideClass d x).1) :=
      hcap.trans_le (le_max_left _ _)
    simpa only [Rat.cast_zero] using (Rat.cast_lt (K := ℝ)).mpr hh
  have hg : (lower data (canonicalOutsideClass d x).1 : ℝ) ≤ 1/2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (hbins.trans hlow)
    norm_num at hh
    exact hh
  have hu : (upper data (canonicalOutsideClass d x).1 : ℝ) ≤ 1/2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hlow
    norm_num at hh
    exact hh
  have hden' : 1-(lower data (canonicalOutsideClass d x).1 : ℝ) ≤ den := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (le_max_right data.cap (1-lower data (canonicalOutsideClass d x).1))
    simpa only [Rat.cast_sub,Rat.cast_one] using hh
  have hsum : (∑ c, binWeight d data beta adj c x) =
      (∑ c : CanonicalCenters d, if adj c x then (1 : ℝ) else 0)/(beta*den) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    simp only [binWeight]
    split_ifs <;> simp [den]
  rw [hsum]
  apply (div_le_one (mul_pos hbeta hden)).mpr
  nlinarith

theorem bin_loads_low (d : Coordinates B U q) (data : ProfileData q) (beta : ℝ)
    (adj : CanonicalCenters d → CanonicalOutsides d → Prop)
    (hbeta : 0 < beta) (hcap : 0 < data.cap) (ha : 0 ≤ data.alpha) (ho : data.omega ≤ 1)
    (x : CanonicalOutsides d) (hcol : (∑ c, binWeight d data beta adj c x) ≤ 1) :
    RandomOrderMatching.Analysis.Repair.Typed.primaryLoad (data.alpha : ℝ) (binWeight d data beta adj) x ≤ 1 ∧
    RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad (data.omega : ℝ) (binWeight d data beta adj) x ≤ 1 := by
  have hA : (0 : ℝ) ≤ data.alpha := by exact_mod_cast ha
  have hO : (data.omega : ℝ) ≤ 1 := by exact_mod_cast ho
  constructor
  · apply le_trans _ hcol
    apply Finset.sum_le_sum
    intro c _
    have hw := binWeight_nonneg d data beta adj hbeta hcap c x
    apply mul_le_of_le_one_left hw
    rcases c with g | m | p | i | j <;>
      simp [RandomOrderMatching.Analysis.Repair.Typed.primaryRate] <;> linarith
  · apply le_trans _ hcol
    apply Finset.sum_le_sum
    intro c _
    have hw := binWeight_nonneg d data beta adj hbeta hcap c x
    apply mul_le_of_le_one_left hw
    rcases c with g | m | p | i | j <;>
      simp [RandomOrderMatching.Analysis.Repair.Typed.secondaryRate,hO]

end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.minimumMask_identity
#print axioms RandomOrderMatching.Analysis.Profile.minimumMask_allowed
#print axioms RandomOrderMatching.Analysis.Profile.bin_loads_low
