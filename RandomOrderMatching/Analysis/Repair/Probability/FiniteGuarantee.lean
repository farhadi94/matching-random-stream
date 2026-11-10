import RandomOrderMatching.Analysis.Repair.Probability.AggregateEvents
import RandomOrderMatching.Analysis.Repair.Probability.Parameters
import RandomOrderMatching.Analysis.Repair.Probability.ReferenceData

/-! The simultaneous actual repair theorem for the finite original-parent
categorical experiment. All local and aggregate events are proved above;
only deterministic graph/reference/transfer data remain as inputs. -/
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair.Probability
open RandomOrderMatching.Analysis.Repair RandomOrderMatching.Analysis.Repair.Typed
variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]
namespace LocalData
variable (D : LocalData (B:=B) (G:=G) (M:=M) (P:=P) (I:=I) (J:=J) (R:=R) (U:=U))

def transfer (V : (B→Clock)→ℝ) (z : B→Clock) : Prop :=
  (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj (states D.parents z) D.H D.sideC D.sideO false)):ℝ)+
  (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj (states D.parents z) D.H D.sideC D.sideO true)):ℝ)+
  ((selectedEdges (P:=P) (I:=I) (U:=U) (states D.parents z)).card:ℝ)≤2*V z

lemma profile_on_events {μ ε t : ℝ} (hε : 0≤ε)
    (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hpairs : (Fintype.card R:ℝ)+(Fintype.card M:ℝ)+(Fintype.card G:ℝ)≤μ)
    (V : (B→Clock)→ℝ) (z : B→Clock)
    (htransfer : D.transfer V z) (hbase : (Fintype.card (Centers G M P I J):ℝ)≤V z)
    (hl : z∉⋃i,D.localBad ε i) (ha : z∉⋃i,D.aggregateBad t i) :
    max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w-1000*ε*μ-3*t)≤V z := by
  have hloads := D.local_events_imply_loads hε z hl
  have hevents := D.aggregate_events_imply_counts t z ha
  have hmain := actual_profile_bound (states D.parents z) alpha omega parameters.1 parameters.2
    D.H D.sideC D.sideO D.w D.nonneg (centerError ε) (outsideError D.w ε)
    (fun _ _=>hε) (outsideError_nonneg D.w hε) hloads.1 hloads.2
    t t t t (2*t) (V z) hevents.1 hevents.2.1 hevents.2.2.1 hevents.2.2.2.1 hevents.2.2.2.2
    htransfer hbase
  have herr := local_error_sum_le D.w D.nonneg D.row_capacity hε hcenters hpairs
  have hvalue := (le_max_right _ _).trans hmain
  apply max_le hbase
  unfold totalError at hvalue
  linarith

theorem profile_failure_bound {μ ε t : ℝ} (hε : 0<ε) (ht : 0<t) (hμ : 0<μ)
    (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hcount : randomPairCount G M J R≤μ)
    (hblock : ∀b,originalMultiplicity D.parents b≤D.kappa)
    (V : (B→Clock)→ℝ) (htransfer : ∀z,D.transfer V z)
    (hbase : ∀z,(Fintype.card (Centers G M P I J):ℝ)≤V z) :
    (experiment (B:=B)).real {z | V z<max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w-1000*ε*μ-3*t)}≤
      8*μ*Real.exp (-ε^2*D.beta/(4000*D.kappa))+
      5*Real.exp (-2*t^2/((D.kappa:ℝ)*μ)) := by
  have hpairs : (Fintype.card R:ℝ)+(Fintype.card M:ℝ)+(Fintype.card G:ℝ)≤μ := by
    unfold randomPairCount at hcount
    have hj : (0:ℝ)≤Fintype.card J := Nat.cast_nonneg _
    linarith
  have hs : {z | V z<max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w-1000*ε*μ-3*t)}⊆
      (⋃i,D.localBad ε i)∪(⋃i,D.aggregateBad t i) := by
    intro z hz
    by_cases hl : z∈⋃i,D.localBad ε i
    · exact Or.inl hl
    by_cases ha : z∈⋃i,D.aggregateBad t i
    · exact Or.inr ha
    exact False.elim (not_lt_of_ge (D.profile_on_events (le_of_lt hε) hcenters hpairs
      V z (htransfer z) (hbase z) hl ha) hz)
  calc
    _ ≤ (experiment (B:=B)).real ((⋃i,D.localBad ε i)∪(⋃i,D.aggregateBad t i)) := measureReal_mono hs
    _ ≤ (experiment (B:=B)).real (⋃i,D.localBad ε i)+(experiment (B:=B)).real (⋃i,D.aggregateBad t i) :=
      measureReal_union_le _ _
    _ ≤ _ := add_le_add (D.local_failure_union hε hcenters hpairs)
      (D.aggregate_failure_union hblock hcount hμ ht)

/-- Final finite fixed-host repair guarantee at the published parameters.
L and theta are deterministic confidence parameters; the explicit logarithmic
condition is separated from the actual probability calculation. -/
theorem fixed_host_profile_failure {μ N θ L : ℝ}
    (hμ : 0<μ) (hN : 1≤N) (hμN : μ≤N) (hθ : 0<θ) (hθsmall : θ≤1/100)
    (hL : 0<L) (hscale : Real.exp (-L)≤θ/N)
    (hbeta : 10^30*(D.kappa:ℝ)*L/2≤D.beta) (hmuBeta : (49:ℝ)/100*D.beta≤μ)
    (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hcount : randomPairCount G M J R≤μ)
    (hblock : ∀b,originalMultiplicity D.parents b≤D.kappa)
    (V : (B→Clock)→ℝ) (htransfer : ∀z,D.transfer V z)
    (hbase : ∀z,(Fintype.card (Centers G M P I J):ℝ)≤V z) :
    (experiment (B:=B)).real {z | V z<max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w-μ/10000000)}≤5*θ := by
  have hk : (0:ℝ)<D.kappa := Nat.cast_pos.mpr D.kappa_pos
  have hNp : 0<N := by linarith
  have ht : 0<Real.sqrt ((D.kappa:ℝ)*μ*L) := Real.sqrt_pos.mpr (by positivity)
  have hfail := D.profile_failure_bound epsilon_pos ht hμ hcenters hcount hblock V htransfer hbase
  have herr := finite_error_reserve (le_of_lt hk) (le_of_lt hL) hμ hbeta hmuBeta
  have heps := epsilon_pos
  have hsub : {z | V z<max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w-μ/10000000)}⊆
      {z | V z<max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w-1000*epsilon*μ-3*Real.sqrt ((D.kappa:ℝ)*μ*L))} := by
    intro z hz
    change V z<max (Fintype.card (Centers G M P I J):ℝ) (profile alpha omega D.w-μ/10000000) at hz
    change V z<max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w-1000*epsilon*μ-3*Real.sqrt ((D.kappa:ℝ)*μ*L))
    apply lt_of_lt_of_le hz
    apply max_le_max (le_refl _)
    have hs := Real.sqrt_nonneg ((D.kappa:ℝ)*μ*L)
    nlinarith [mul_pos heps hμ]
  have hexp := beta_exponent hk hbeta
  have hlocal : 8*μ*Real.exp (-epsilon^2*D.beta/(4000*D.kappa))≤4*θ := by
    have h1 : Real.exp (-epsilon^2*D.beta/(4000*D.kappa))≤Real.exp (-125*L) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div,neg_mul] using neg_le_neg hexp
    have hs : θ/N≤1/2 := (div_le_iff₀ hNp).mpr (by nlinarith)
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans
      (local_union_numeric (le_of_lt hμ) hNp hμN (le_of_lt hθ) hs (le_of_lt hL) hscale)
  have hag : 5*Real.exp (-2*(Real.sqrt ((D.kappa:ℝ)*μ*L))^2/((D.kappa:ℝ)*μ))≤θ := by
    rw [aggregate_sqrt_exponent hk hμ (le_of_lt hL)]
    have hs : θ/N≤θ := (div_le_iff₀ hNp).mpr (by nlinarith)
    exact aggregate_union_numeric (le_of_lt hθ) (by linarith) (hscale.trans hs)
  exact (measureReal_mono hsub).trans (hfail.trans (by linarith))

end LocalData
end RandomOrderMatching.Analysis.Repair.Probability
