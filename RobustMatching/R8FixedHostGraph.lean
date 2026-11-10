import RobustMatching.R8FixedHostCoordinates
import RobustMatching.R8FixedHostAnalytic
import RobustMatching.R8FixedHostSupportConsequences
import RobustMatching.R7SupportFlowMapComplete

/-! Instantiation of the analytic repair theorem from actual graph degrees.
The degree bins, affine masks, repair weights, and matrix certificate are
constructed by the imported graph theorem rather than assumed. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
open Classical MeasureTheory
open scoped BigOperators
namespace RobustMatching.R8FixedHost
open R2Cut R7SupportFlowMap R7ClosedRepair.TypedLabeling R8RepairProbability
open R7ClosedRepair.Typed
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]
variable (M H : Graph V) (hM : Matching M) (C : Finset V) (A : Graph V)
  (beta : ℝ)

def canonicalCoordinates :=
  coordinatesFromMatching M hM C A (actualDegreeBin H beta)
    (actualMinimumMask M hM C A (actualDegreeBin H beta) H beta)

local notation "d" => canonicalCoordinates M H hM C A beta
local notation "bin" => actualDegreeBin H beta
local notation "mask" => actualMinimumMask M hM C A bin H beta

theorem fiberMultiplicity_le (par : M→B) (κ : ℕ)
    (hfiber : ∀b,Fintype.card {e:M //par e=b}≤κ) (b : B) :
    originalMultiplicity (fiberParents d par) b≤(κ:ℝ) := by
  apply (fiber_originalMultiplicity_le d par b).trans
  have heq : (∑e:M,if par e=b then (1:ℝ) else 0)=
      (Fintype.card {e:M //par e=b}:ℝ) := by simp [Fintype.card_subtype]
  rw [heq]
  exact_mod_cast hfiber b

def graphLocalData (par : M→B) (b0 : B) (κ : ℕ) (hk : 0<κ)
    (hfiber : ∀b,Fintype.card {e:M //par e=b}≤κ)
    (side : V→Bool)
    (hcross : ∀u v,(R7GraphKonig.simpleGraph H).Adj u v→side u≠side v)
    (hbeta : 0<beta)
    (hcover : ∀e∈H,∃v∈e.val,v∈C)
    (hupper : ∀e∈H,incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1)≤beta) :
    LocalData (B:=B) (G:=PairFiber d .gate) (M:=PairFiber d .missing)
      (P:=CenterUnmatched d) (I:=PairFiber d .internalAvailable)
      (J:=PairFiber d .internalMissing) (R:=PairFiber d .root) (U:=OutsideUnmatched d) :=
  referenceLocalData (fiberParents d par) b0
    (actualReferenceAdj M hM C A bin mask H)
    (fun c=>side (actualVertexEquiv M hM C A bin mask (.inl c)))
    (fun x=>side (actualVertexEquiv M hM C A bin mask (.inr x)))
    (by
      intro c x hx
      have ha := (R8FixedHostSupport.actual_reference_adj_iff M hM C A bin mask H c x).mp hx
      exact hcross _ _ ha.symm)
    beta
    (fun x=>incidenceDegree H (actualVertexEquiv M hM C A bin mask (.inr x))/beta)
    (fun c=>incidenceDegree H (actualVertexEquiv M hM C A bin mask (.inl c)))
    (R8FixedHostSupport.actual_reference_supportData M hM C A bin mask H beta hbeta hcover hupper)
    κ hk (fiberMultiplicity_le M H hM C A beta par κ hfiber)

theorem graphLocalData_weight (par : M→B) (b0 : B) (κ : ℕ) (hk : 0<κ)
    (hfiber : ∀b,Fintype.card {e:M //par e=b}≤κ)
    (side : V→Bool)
    (hcross : ∀u v,(R7GraphKonig.simpleGraph H).Adj u v→side u≠side v)
    (hbeta : 0<beta) (hcover : ∀e∈H,∃v∈e.val,v∈C)
    (hupper : ∀e∈H,incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1)≤beta) :
    (graphLocalData M H hM C A beta par b0 κ hk hfiber side hcross hbeta hcover hupper).w=
      actualRepairWeight M hM C A bin mask H beta := by
  exact R8FixedHostSupport.referenceWeight_eq_actualRepairWeight M hM C A mask bin H beta

theorem graph_analytic_ratio_failure
    (par : M→B) (b0 : B) (κ : ℕ) (hk : 0<κ)
    (hfiber : ∀b,Fintype.card {e:M //par e=b}≤κ)
    (side : V→Bool)
    (hcross : ∀u v,(R7GraphKonig.simpleGraph H).Adj u v→side u≠side v)
    (hbeta : 0<beta) (hcover : ∀e∈H,∃v∈e.val,v∈C)
    (hupper : ∀e∈H,incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1)≤beta)
    (hpairLower : ∀e∈M,actualPairKind C A e=.root ∨ actualPairKind C A e=.missing ∨
      actualPairKind C A e=.internalMissing → beta*(1-(R7ReductionCertificate.Concrete.data.lam:ℝ))≤
      incidenceDegree H (orientedEndpoint C e 0)+incidenceDegree H (orientedEndpoint C e 1))
    (hpairUpper : ∀e∈M,actualPairKind C A e=.internalAvailable →
      incidenceDegree H (orientedEndpoint C e 0)+incidenceDegree H (orientedEndpoint C e 1)≤beta)
    {N θ L : ℝ} (hμ : 0<M.card) (hN : 1≤N) (hμN : (M.card:ℝ)≤N)
    (hθ : 0<θ) (hθsmall : θ≤1/100) (hL : 0<L) (hscale : Real.exp (-L)≤θ/N)
    (hsize : 10^30*(κ:ℝ)*L/2≤beta) (hmuBeta : (49:ℝ)/100*beta≤M.card)
    (hcenters : C.card≤M.card) :
    let D := graphLocalData M H hM C A beta par b0 κ hk hfiber side hcross hbeta hcover hupper
    (experiment (B:=B)).real {z | analyticValue D z<
      ((R7ReductionCertificate.Concrete.target:ℝ)-1/10000000)*(M.card:ℝ)}≤5*θ := by
  dsimp only
  let D := graphLocalData M H hM C A beta par b0 κ hk hfiber side hcross hbeta hcover hupper
  have hcard : Fintype.card (CanonicalCenters d)=C.card :=
    actual_center_card M hM C A bin mask
  have hc : (Fintype.card (CanonicalCenters d):ℝ)≤M.card := by
    rw [hcard]; exact_mod_cast hcenters
  apply analytic_ratio_failure D (Nat.cast_pos.mpr hμ) hN hμN hθ hθsmall hL hscale hsize hmuBeta
    hc (canonical_randomPairCount_le M hM C A bin mask)
    (fiberMultiplicity_le M H hM C A beta par κ hfiber)
  have hg := actual_graph_profile_certificate M H hM C A beta hbeta hcover hupper hpairLower hpairUpper
  rw [hcard]
  change _ ≤ max (C.card:ℝ) (profile alpha omega D.w)
  rw [graphLocalData_weight M H hM C A beta par b0 κ hk hfiber side hcross hbeta hcover hupper]
  change _ ≤ max (C.card:ℝ)
    (profile (R7ReductionCertificate.Concrete.data.alpha:ℝ)
      (R7ReductionCertificate.Concrete.data.omega:ℝ)
      (actualRepairWeight M hM C A bin mask H beta)) at hg
  have ha : (R7ReductionCertificate.Concrete.data.alpha:ℝ)=alpha := by
    norm_num [alpha,R7ReductionCertificate.Concrete.data]
  have ho : (R7ReductionCertificate.Concrete.data.omega:ℝ)=omega := by
    norm_num [omega,R7ReductionCertificate.Concrete.data]
  rw [ha,ho] at hg
  exact hg

end RobustMatching.R8FixedHost
