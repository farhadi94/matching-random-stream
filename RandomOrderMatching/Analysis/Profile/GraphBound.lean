import RandomOrderMatching.Analysis.Profile.MaskAdmissibility
import RandomOrderMatching.Analysis.Profile.GraphGeometry
import RandomOrderMatching.Analysis.Profile.ProfileIdentity

noncomputable section
set_option maxHeartbeats 0
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Graph RandomOrderMatching.Certificates.DegreeProfile
open RandomOrderMatching.Analysis.Repair.Labeling

section Actual
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (M : Graph V) (hM : Matching M) (C : Finset V) (available : Graph V)
  (bin : V → Fin 152) (mask : V → Fin 4)
local notation "D" => coordinatesFromMatching M hM C available bin mask

theorem actual_centerCount : centerCount (vertexColumn D) = (C.card : ℝ) := by
  calc
    _ = ∑ v : CanonicalVertex D, centerMark (vertexColumn D (coordinateEquiv D v)) := by
      exact ((coordinateEquiv D).sum_comp (fun v => centerMark (vertexColumn D v))).symm
    _ = ∑ _c : CanonicalCenters D, (1 : ℝ) := by
      rw [Fintype.sum_sum_type]
      have hc (c : CanonicalCenters D) : centerMark (vertexColumn D (coordinateEquiv D (.inl c)))=1 := by
        rw [coordinate_vertex_column]
        exact if_pos (by trivial)
      have hx (x : CanonicalOutsides D) : centerMark (vertexColumn D (coordinateEquiv D (.inr x)))=0 := by
        rw [coordinate_vertex_column]
        exact if_neg (by intro h; exact h)
      simp_rw [hc,hx]
      simp only [Finset.sum_const_zero,add_zero]
    _ = (Fintype.card (CanonicalCenters D) : ℝ) := by rw [Finset.sum_const,Finset.card_univ]; simp only [nsmul_eq_mul,mul_one]
    _ = _ := by rw [actual_center_card]

def actualRepairWeight (H : Graph V) (beta : ℝ) : CanonicalCenters D → CanonicalOutsides D → ℝ :=
  RandomOrderMatching.Analysis.Repair.Typed.referenceWeight
    (fun x c => actualReferenceAdj M hM C available bin mask H c x) beta (Concrete.data.cap : ℝ)
    (fun x => incidenceDegree H (actualVertexEquiv M hM C available bin mask (.inr x))/beta)

/-- Exact graph-level profile inequality. The chosen mask hypothesis is a
pointwise definition of the four possible affine arms, not an assumed
profile or a feasible-vector certificate. -/
theorem actual_graph_profile_bound
    (H : Graph V) (beta : ℝ) (hbeta : 0 < beta) (hmu : 0 < (M.card : ℝ))
    (hcover : ∀ e∈H, ∃ v∈e.val, v∈C)
    (hbin : ∀ v, beta*(lower Concrete.data (bin v) : ℝ) ≤ incidenceDegree H v ∧
      incidenceDegree H v ≤ beta*(upper Concrete.data (bin v) : ℝ))
    (hedge : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta)
    (hpairLower : ∀ e∈M, actualPairKind C available e=.root ∨
      actualPairKind C available e=.missing ∨ actualPairKind C available e=.internalMissing →
      beta*(1-(Concrete.data.lam : ℝ)) ≤ incidenceDegree H (orientedEndpoint C e 0)+
        incidenceDegree H (orientedEndpoint C e 1))
    (hpairUpper : ∀ e∈M, actualPairKind C available e=.internalAvailable →
      incidenceDegree H (orientedEndpoint C e 0)+incidenceDegree H (orientedEndpoint C e 1) ≤ beta)
    (hmask : ∀ x : CanonicalOutsides D, (D).mask (coordinateEquiv D (.inr x)) =
      loadMask Concrete.data (outsideType D x)
        (RandomOrderMatching.Analysis.Repair.Typed.primaryLoad (Concrete.data.alpha : ℝ)
          (binWeight D Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x)
        (RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad (Concrete.data.omega : ℝ)
          (binWeight D Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x)) :
    (Concrete.target : ℝ)*(M.card : ℝ) ≤ max (C.card : ℝ)
      (RandomOrderMatching.Analysis.Repair.Typed.profile (Concrete.data.alpha : ℝ) (Concrete.data.omega : ℝ)
        (actualRepairWeight M hM C available bin mask H beta)) := by
  have hv := actual_mask_admissibility M hM C available bin mask H beta hbeta
    (fun v => (hbin v).2) hmask
  have hg := actual_profile_geometry M H hM C available bin mask beta hbeta hcover hbin hv
    hedge hpairLower hpairUpper
  have hm : 0 < (Fintype.card M : ℝ) := by simpa using hmu
  have hb := concrete_graph_profile_bound D (actualReference M H hM C available bin mask)
    (actualLeft M H hM C) (actualRight M H hM C) beta hg hbeta hm
  rw [actual_centerCount M hM C available bin mask] at hb
  have hp := rawProfile_eq_bin_profile D (actualReference M H hM C available bin mask)
    Concrete.data beta (actualReferenceAdj M hM C available bin mask H) hbeta
    (by norm_num [Concrete.data]) (by norm_num [Concrete.data])
    (actual_reference_phase_sum M hM C available bin mask H Concrete.data) hmask
  rw [hp] at hb
  have hw := typed_profile_mono (Concrete.data.alpha : ℝ) (Concrete.data.omega : ℝ)
    (binWeight D Concrete.data beta (actualReferenceAdj M hM C available bin mask H))
    (actualRepairWeight M hM C available bin mask H beta)
    (by norm_num [Concrete.data]) (by norm_num [Concrete.data])
    (actual_binWeight_le_referenceWeight M hM C available bin mask H Concrete.data beta
      (fun v => incidenceDegree H v/beta) hbeta (by norm_num [Concrete.data])
      (fun v => (le_div_iff₀ hbeta).mpr (by simpa [mul_comm] using (hbin v).1)))
  simpa using hb.trans (max_le_max le_rfl hw)

end Actual
end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.actual_graph_profile_bound
