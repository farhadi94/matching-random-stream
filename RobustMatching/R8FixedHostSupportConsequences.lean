import RobustMatching.R8FixedHostSupport
import RobustMatching.R7SupportFlowMapActualProfile

noncomputable section
set_option maxHeartbeats 0
open Classical
namespace RobustMatching.R8FixedHostSupport
open RobustMatching.R2Cut RobustMatching.R1Gate RobustMatching.R7GraphKonig
open RobustMatching.R7SupportFlowMap
open RobustMatching.R7ClosedRepair.TypedLabeling

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
variable (M : Graph V) (hM : Matching M) (C : Finset V) (available : Graph V)
  (bin : V → Fin q) (mask : V → Fin 4)
local notation "D" => coordinatesFromMatching M hM C available bin mask

theorem actual_normalized_degree_lt_one (H : Graph V) (beta : ℝ) (hbeta : 0 < beta)
    (hupper : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta) (v : V) :
    incidenceDegree H v/beta < 1 := by
  simpa only [incidenceDegree_eq_simpleGraph] using
    normalized_degree_lt_one (simpleGraph H) hbeta (actual_upper_simpleGraph C H beta hupper) v

theorem actual_degree_lt_beta (H : Graph V) (beta : ℝ) (hbeta : 0 < beta)
    (hupper : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta) (v : V) :
    incidenceDegree H v < beta :=
  (div_lt_one hbeta).mp (actual_normalized_degree_lt_one C H beta hbeta hupper v)

theorem actual_outside_degree_eq_count (H : Graph V) (beta : ℝ) (hbeta : 0 < beta)
    (hcover : ∀ e∈H, ∃ v∈e.val, v∈C)
    (hupper : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta) (x : CanonicalOutsides D) :
    incidenceDegree H (actualVertexEquiv M hM C available bin mask (.inr x)) =
      ((Finset.univ.filter fun c : CanonicalCenters D =>
        actualReferenceAdj M hM C available bin mask H c x).card : ℝ) := by
  have hh := (actual_reference_supportData M hM C available bin mask H beta hbeta hcover hupper).row_degree x
  have he : beta*(incidenceDegree H (actualVertexEquiv M hM C available bin mask (.inr x))/beta)=
      incidenceDegree H (actualVertexEquiv M hM C available bin mask (.inr x)) := by
    field_simp [ne_of_gt hbeta]
  rw [he] at hh
  exact hh.symm

theorem actual_outside_degree_le_cover (H : Graph V) (beta : ℝ) (hbeta : 0 < beta)
    (hcover : ∀ e∈H, ∃ v∈e.val, v∈C)
    (hupper : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta) (x : CanonicalOutsides D) :
    incidenceDegree H (actualVertexEquiv M hM C available bin mask (.inr x)) ≤ C.card := by
  rw [actual_outside_degree_eq_count M hM C available bin mask H beta hbeta hcover hupper x]
  have hh := Finset.card_le_card (Finset.filter_subset
    (fun c : CanonicalCenters D => actualReferenceAdj M hM C available bin mask H c x) Finset.univ)
  have hc : (Finset.univ : Finset (CanonicalCenters D)).card=C.card := by
    rw [Finset.card_univ,actual_center_card]
  exact_mod_cast hh.trans_eq hc

theorem referenceWeight_eq_actualRepairWeight
    (bin : V → Fin 152) (H : Graph V) (beta : ℝ) :
    RobustMatching.R7ClosedRepair.Typed.referenceWeight
      (fun x c => actualReferenceAdj M hM C available bin mask H c x) beta (1/100)
      (fun x => incidenceDegree H (actualVertexEquiv M hM C available bin mask (.inr x))/beta) =
      actualRepairWeight M hM C available bin mask H beta := by
  unfold actualRepairWeight
  have hc : (RobustMatching.R7ReductionCertificate.Concrete.data.cap : ℝ)=1/100 := by
    norm_num [RobustMatching.R7ReductionCertificate.Concrete.data]
  rw [hc]

end RobustMatching.R8FixedHostSupport

#print axioms RobustMatching.R8FixedHostSupport.actual_normalized_degree_lt_one
#print axioms RobustMatching.R8FixedHostSupport.actual_outside_degree_eq_count
#print axioms RobustMatching.R8FixedHostSupport.actual_outside_degree_le_cover
#print axioms RobustMatching.R8FixedHostSupport.referenceWeight_eq_actualRepairWeight
