import RandomOrderMatching.Analysis.Repair.Probability.FiniteGuarantee

/-! The analytic value used before comparison with an actual phase bank.
It is defined for every original-parent clock outcome. In particular, the
repair theorem is never conditioned on a cutoff bracket. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical MeasureTheory
namespace RandomOrderMatching.Analysis.FixedHost
open RandomOrderMatching.Analysis.Repair.Probability RandomOrderMatching.Analysis.Repair.Typed
variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]

variable (D : LocalData (B:=B) (G:=G) (M:=M) (P:=P) (I:=I) (J:=J) (R:=R) (U:=U))

def analyticValue (z : B→Clock) : ℝ :=
  max (Fintype.card (Centers G M P I J):ℝ)
    (((RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges
      (deletionAdj (states D.parents z) D.H D.sideC D.sideO false)):ℝ)+
     (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges
      (deletionAdj (states D.parents z) D.H D.sideC D.sideO true)):ℝ)+
     ((selectedEdges (P:=P) (I:=I) (U:=U) (states D.parents z)).card:ℝ))/2)

theorem analyticValue_base (z : B→Clock) :
    (Fintype.card (Centers G M P I J):ℝ)≤analyticValue D z := le_max_left _ _

theorem analyticValue_transfer (z : B→Clock) :
    D.transfer (analyticValue D) z := by
  have h := le_max_right (Fintype.card (Centers G M P I J):ℝ)
    (((RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges
      (deletionAdj (states D.parents z) D.H D.sideC D.sideO false)):ℝ)+
     (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges
      (deletionAdj (states D.parents z) D.H D.sideC D.sideO true)):ℝ)+
     ((selectedEdges (P:=P) (I:=I) (U:=U) (states D.parents z)).card:ℝ))/2)
  change _≤2*analyticValue D z
  change _≤analyticValue D z at h
  linarith

theorem analyticValue_le {z : B→Clock} {v : ℝ}
    (hbase : (Fintype.card (Centers G M P I J):ℝ)≤v)
    (htransfer : D.transfer (fun _=>v) z) : analyticValue D z≤v := by
  apply max_le hbase
  change _≤2*v at htransfer
  linarith

theorem analytic_failure {μ N θ L : ℝ}
    (hμ : 0<μ) (hN : 1≤N) (hμN : μ≤N) (hθ : 0<θ) (hθsmall : θ≤1/100)
    (hL : 0<L) (hscale : Real.exp (-L)≤θ/N)
    (hbeta : 10^30*(D.kappa:ℝ)*L/2≤D.beta) (hmuBeta : (49:ℝ)/100*D.beta≤μ)
    (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hcount : randomPairCount G M J R≤μ)
    (hblock : ∀b,originalMultiplicity D.parents b≤D.kappa) :
    (experiment (B:=B)).real {z | analyticValue D z<
      max (Fintype.card (Centers G M P I J):ℝ)
        (profile alpha omega D.w-μ/10000000)}≤5*θ :=
  D.fixed_host_profile_failure hμ hN hμN hθ hθsmall hL hscale hbeta hmuBeta
    hcenters hcount hblock (analyticValue D) (analyticValue_transfer D) (analyticValue_base D)

theorem analytic_ratio_failure {μ N θ L r : ℝ}
    (hμ : 0<μ) (hN : 1≤N) (hμN : μ≤N) (hθ : 0<θ) (hθsmall : θ≤1/100)
    (hL : 0<L) (hscale : Real.exp (-L)≤θ/N)
    (hbeta : 10^30*(D.kappa:ℝ)*L/2≤D.beta) (hmuBeta : (49:ℝ)/100*D.beta≤μ)
    (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hcount : randomPairCount G M J R≤μ)
    (hblock : ∀b,originalMultiplicity D.parents b≤D.kappa)
    (hcertificate : r*μ≤max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w)) :
    (experiment (B:=B)).real {z | analyticValue D z<(r-1/10000000)*μ}≤5*θ := by
  apply (measureReal_mono (show {z | analyticValue D z<(r-1/10000000)*μ}⊆
    {z | analyticValue D z<max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w-μ/10000000)} from ?_)).trans
    (analytic_failure D hμ hN hμN hθ hθsmall hL hscale hbeta hmuBeta hcenters hcount hblock)
  intro z hz
  change analyticValue D z<(r-1/10000000)*μ at hz
  change analyticValue D z<max (Fintype.card (Centers G M P I J):ℝ)
    (profile alpha omega D.w-μ/10000000)
  apply lt_of_lt_of_le hz
  have ha := le_max_left (Fintype.card (Centers G M P I J):ℝ)
    (profile alpha omega D.w-μ/10000000)
  have hb := le_max_right (Fintype.card (Centers G M P I J):ℝ)
    (profile alpha omega D.w-μ/10000000)
  rcases le_max_iff.mp hcertificate with hc|hc <;> nlinarith

end RandomOrderMatching.Analysis.FixedHost
