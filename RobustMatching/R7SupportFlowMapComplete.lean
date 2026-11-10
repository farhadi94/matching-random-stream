import RobustMatching.R7SupportFlowMapActualProfile
import RobustMatching.R7SupportFlowMapActualMaskChoice

/-! Complete deterministic graph-to-profile certificate. The degree bins
and minimizing affine masks are explicitly constructed. No matrix rows,
certificate validity, profile inequality, or mask existence are premises. -/
noncomputable section
set_option maxHeartbeats 0
open scoped BigOperators
open Classical
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R2Cut RobustMatching.R7ReductionCertificate
open RobustMatching.R7ClosedRepair.TypedLabeling

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem actual_graph_degree_le (H : Graph V) (C : Finset V) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hedge : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta) (v : V) :
    incidenceDegree H v ≤ beta := by
  by_cases hv : ∃ e∈H, v∈e.val
  · obtain ⟨e,he,hve⟩ := hv
    obtain ⟨i,hi⟩ := orientedEndpoint_surjective C e v hve
    have hh := hedge e he
    have h0 := incidenceDegree_nonneg H (orientedEndpoint C e 0)
    have h1 := incidenceDegree_nonneg H (orientedEndpoint C e 1)
    fin_cases i
    · change orientedEndpoint C e 0=v at hi
      rw [hi] at hh
      linarith
    · change orientedEndpoint C e 1=v at hi
      rw [hi] at hh
      linarith
  · have hz : incidenceDegree H v=0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hn : v∉e.val := fun h => hv ⟨e,he,h⟩
      simp [hn]
    simpa only [hz] using hbeta

def actualDegreeBin (H : Graph V) (beta : ℝ) (v : V) : Fin 152 :=
  if h : 0 ≤ incidenceDegree H v/beta ∧ incidenceDegree H v/beta ≤ 1 then
    concreteBin (incidenceDegree H v/beta) h.1 h.2 else 0

theorem actualDegreeBin_bounds (H : Graph V) (beta : ℝ) (hbeta : 0 < beta)
    (hdegree : ∀ v, incidenceDegree H v ≤ beta) (v : V) :
    beta*(lower Concrete.data (actualDegreeBin H beta v) : ℝ) ≤ incidenceDegree H v ∧
      incidenceDegree H v ≤ beta*(upper Concrete.data (actualDegreeBin H beta v) : ℝ) := by
  have h0 : 0 ≤ incidenceDegree H v/beta := div_nonneg (incidenceDegree_nonneg H v) hbeta.le
  have h1 : incidenceDegree H v/beta ≤ 1 := (div_le_one hbeta).mpr (hdegree v)
  have h := concreteBin_bounds (incidenceDegree H v/beta) h0 h1
  have hc : 0 ≤ incidenceDegree H v/beta ∧ incidenceDegree H v/beta ≤ 1 := ⟨h0,h1⟩
  rw [actualDegreeBin,dif_pos hc]
  exact ⟨by simpa [mul_comm] using (le_div_iff₀ hbeta).mp h.1,
    by simpa [mul_comm] using (div_le_iff₀ hbeta).mp h.2⟩

def actualCanonicalProfile (M : Graph V) (hM : Matching M) (C : Finset V)
    (available H : Graph V) (beta : ℝ) : ℝ :=
  let bin := actualDegreeBin H beta
  let mask := actualMinimumMask M hM C available bin H beta
  RobustMatching.R7ClosedRepair.Typed.profile (Concrete.data.alpha : ℝ) (Concrete.data.omega : ℝ)
    (actualRepairWeight M hM C available bin mask H beta)

/-- The exact internal-152 inequality for an actual finite graph. The
benchmark need only be a matching; the graph may have internal cover
edges, internal benchmark pairs, and arbitrarily many isolated vertices. -/
theorem actual_graph_profile_certificate
    (M H : Graph V) (hM : Matching M) (C : Finset V) (available : Graph V)
    (beta : ℝ) (hbeta : 0 < beta)
    (hcover : ∀ e∈H, ∃ v∈e.val, v∈C)
    (hedge : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta)
    (hpairLower : ∀ e∈M, actualPairKind C available e=.root ∨
      actualPairKind C available e=.missing ∨ actualPairKind C available e=.internalMissing →
      beta*(1-(Concrete.data.lam : ℝ)) ≤ incidenceDegree H (orientedEndpoint C e 0)+
        incidenceDegree H (orientedEndpoint C e 1))
    (hpairUpper : ∀ e∈M, actualPairKind C available e=.internalAvailable →
      incidenceDegree H (orientedEndpoint C e 0)+incidenceDegree H (orientedEndpoint C e 1) ≤ beta) :
    (Concrete.target : ℝ)*(M.card : ℝ) ≤
      max (C.card : ℝ) (actualCanonicalProfile M hM C available H beta) := by
  by_cases hmu : 0 < (M.card : ℝ)
  · exact actual_graph_profile_bound M hM C available (actualDegreeBin H beta)
      (actualMinimumMask M hM C available (actualDegreeBin H beta) H beta)
      H beta hbeta hmu hcover
      (actualDegreeBin_bounds H beta hbeta (actual_graph_degree_le H C beta hbeta.le hedge))
      hedge hpairLower hpairUpper
      (actualMinimumMask_identity M hM C available (actualDegreeBin H beta) H beta)
  · have hz : (M.card : ℝ)=0 := by
      have hn : (0 : ℝ) ≤ M.card := by positivity
      linarith
    rw [hz,mul_zero]
    exact (show (0 : ℝ) ≤ C.card by positivity).trans (le_max_left _ _)

end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.actual_graph_profile_certificate
