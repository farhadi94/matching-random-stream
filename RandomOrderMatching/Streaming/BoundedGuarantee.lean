import RandomOrderMatching.Streaming.ApproximationRatio
import RandomOrderMatching.Acquisition.Probability.SuffixGuarantee

/-! Complete local bounded-integer contract for the actual unknown-length
streaming machine. All acquisition, stopped-history, fixed-host, operational,
clamping, confidence and finite-permutation interfaces are instantiated. -/
noncomputable section
open Classical
open scoped BigOperators
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Weights.Windows
open RandomOrderMatching.Phases.Execution RandomOrderMatching.Acquisition.Probability
variable {V : Type*} [Fintype V] [LinearOrder V]
set_option maxHeartbeats 0

/-- The final unconditional bounded-integer contract. There is no supplied
cap-success, fixed-host, stopping-history, feasibility or probability premise. -/
theorem confidentMachine_contract (W : ℕ) (hW : 0 < W)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1) :
    (confidentMachine (V:=V) W delta hW).Contract W finalRatio delta := by
  apply confidentMachine_contract_of_suffix_lift W hW delta hd hd1
  intro m hm w hw label hi h
  dsimp only
  intro _hlarge
  let L := confidenceLog (Fintype.card V) W delta
  let Q := canonicalBudget V W L
  let LU := capLog (Fintype.card V) W Q delta
  let cfg := canonicalSelectedConfig (V:=V) W L LU m hW (confidenceLog_pos _ _ _)
  let N : ℝ := confidenceVertices (Fintype.card V) W
  have hL : 1 ≤ L := confidenceLog_pos _ _ _
  have hb : (cfg.beta:ℝ) ≤ RandomOrderMatching.Analysis.BalancedCut.beta0 W L := by
    rw [canonicalSelectedConfig_beta]
    norm_num [RandomOrderMatching.Analysis.BalancedCut.beta0]
  have hlo : cfg.lower=RandomOrderMatching.Analysis.FixedHost.lowerThreshold W L := rfl
  have hN : 2 ≤ N := by
    dsimp [N,confidenceVertices]
    exact_mod_cast le_max_left 2 (Fintype.card V*W)
  have hv : (Fintype.card (V×Fin W):ℝ) ≤ N := by
    dsimp [N,confidenceVertices]
    simp only [Fintype.card_prod,Fintype.card_fin]
    exact_mod_cast le_max_right 2 (Fintype.card V*W)
  have hh := canonical_physical_suffix_failure_probability (n:=m) (W:=W) (L:=L) hm hW hL cfg hb hlo w hw
    (Classical.choice h) label (decode w (Finset.univ.image label)) (decode_matching w (Finset.univ.image label))
    (decode_subset w (Finset.univ.image label)) (N:=N) (δ:=delta) hN hv hd hd1 (confidenceLog_spec (Fintype.card V) W hd hd1)
  exact hh

/-- Random-order success for every actual simple input list. The range
condition is local to that input, as required by weight-window reduction. -/
theorem bounded_integer_random_order (W : ℕ) (hW : 0 < W)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (w : Edge V → ℕ) (l : List (Edge V)) (hnd : l.Nodup)
    (hw : ∀ e ∈ l,1 ≤ w e ∧ w e ≤ W) :
    RandomOrderMatching.Probability.Restriction.permMean l (fun u =>
      if (confidentMachine (V:=V) W delta hW).Good finalRatio w u then 0 else 1) ≤ delta :=
  (confidentMachine_contract W hW delta hd hd1).local_success w l hnd hw

/-- The same algorithm applies to unweighted graphs by fixing W=1. -/
theorem unweighted_random_order (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (l : List (Edge V)) (hnd : l.Nodup) :
    RandomOrderMatching.Probability.Restriction.permMean l (fun u =>
      if (confidentMachine (V:=V) 1 delta (by decide)).Good finalRatio (fun _ => 1) u
      then 0 else 1) ≤ delta := by
  apply bounded_integer_random_order 1 (by decide) delta hd hd1 (fun _ => 1) l hnd
  intro e he
  exact ⟨le_rfl,le_rfl⟩

end RandomOrderMatching.Streaming
