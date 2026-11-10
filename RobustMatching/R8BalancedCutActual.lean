import RobustMatching.R8BalancedCutGraph

/-! Final actual finite-graph interface consumed by acquisition and the
typed support map. Balance is constructed, not supplied as an assumption. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RobustMatching.R8BalancedCut
open RobustMatching.R2Cut RobustMatching.R7GraphKonig RobustMatching.R7GraphComponents
open RobustMatching.R2BalancedCut RobustMatching.R7SupportFlowMap

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The final balanced analytic cut on the actual retained edge sets.
The only graph inequalities assumed are the original acquisition upper
bound on H and non-underfull lower bound on N. -/
theorem actual_balanced_cut
    (G : SimpleGraph V) (w : Sym2 V→ℕ) (W : ℕ)
    (M : Graph V) (hM : Matching M) (H N : Graph (V×Fin W))
    (hH : simpleGraph H≤unfolding G w W)
    (κ L : ℕ) (hk : 1≤κ) (hL : 1≤L) (n δ : ℝ)
    (hn : 2≤n) (hcard : (Fintype.card (V×Fin W) : ℝ)≤n)
    (hδ : 0<δ) (hδ1 : δ<1) (hlog : Real.log (100*n/δ)≤L)
    (hupper : ∀ e∈H,(R8Acquisition.edgeDegree H e : ℝ)≤beta0 κ L)
    (hlower : ∀ e∈N,(1-1/10^9:ℝ)*beta0 κ L≤(R8Acquisition.edgeDegree H e : ℝ)) :
    ∃ z : V→Bool,
      (∀ e∈M,∀ u∈e.val,∀ v∈e.val,u≠v→z u≠z v) ∧
      (simpleGraph (restrict H (fun y=>z y.1))).Colorable 2 ∧
      (∀ x,incidenceDegree H x/2-tolerance*beta0 κ L≤
          incidenceDegree (restrict H (fun y=>z y.1)) x ∧
        incidenceDegree (restrict H (fun y=>z y.1)) x≤
          incidenceDegree H x/2+tolerance*beta0 κ L+1/2) ∧
      (∀ e∈restrict H (fun y=>z y.1),
        (R8Acquisition.edgeDegree (restrict H (fun y=>z y.1)) e : ℝ)≤betaCut (beta0 κ L)) ∧
      (∀ e∈restrict N (fun y=>z y.1),
        (1-1/10^8:ℝ)*betaCut (beta0 κ L)≤
          (R8Acquisition.edgeDegree (restrict H (fun y=>z y.1)) e : ℝ)) := by
  let hu := actual_edge_upper H (beta0 κ L) hupper
  let hl := actual_edge_lower H N ((1-1/10^9:ℝ)*beta0 κ L) hlower
  let z := canonicalCopySide G w W M hM (simpleGraph H) hH κ L hk hL n δ hn hcard
    hδ hδ1 hlog hu
  have hh := canonical_unfolded_cut G w W M hM (simpleGraph H) (simpleGraph N) hH
    κ L hk hL n δ hn hcard hδ hδ1 hlog hu hl
  change
    (∀ e∈M,∀ u∈e.val,∀ v∈e.val,u≠v→z u≠z v) ∧
    (∀ x,((simpleGraph H).degree x : ℝ)/2-tolerance*beta0 κ L≤
        ((cutGraph (simpleGraph H) (fun y=>z y.1)).degree x : ℝ) ∧
      ((cutGraph (simpleGraph H) (fun y=>z y.1)).degree x : ℝ)≤
        ((simpleGraph H).degree x : ℝ)/2+tolerance*beta0 κ L+1/2) ∧
    (∀ x y,(cutGraph (simpleGraph H) (fun y=>z y.1)).Adj x y→
      ((cutGraph (simpleGraph H) (fun y=>z y.1)).degree x : ℝ)+
        (cutGraph (simpleGraph H) (fun y=>z y.1)).degree y≤betaCut (beta0 κ L)) ∧
    (∀ x y,(cutGraph (simpleGraph N) (fun y=>z y.1)).Adj x y→
      (1-1/10^8:ℝ)*betaCut (beta0 κ L)≤
        ((cutGraph (simpleGraph H) (fun y=>z y.1)).degree x : ℝ)+
          (cutGraph (simpleGraph H) (fun y=>z y.1)).degree y) at hh
  refine ⟨z,hh.1,restrict_colorable _ _,?_,?_,?_⟩
  · intro x
    rw [restricted_incidenceDegree,incidenceDegree_eq_simpleGraph]
    exact hh.2.1 x
  · intro e he
    obtain ⟨u,v,hne,hev⟩ := Finset.card_eq_two.mp e.property
    have ha := adj_of_edge he (show u∈e.val by rw [hev]; simp)
      (show v∈e.val by rw [hev]; simp) hne
    rw [simpleGraph_restrict] at ha
    have hb := hh.2.2.1 u v ha
    rw [edgeDegree_of_adj _ e u v hne hev]
    rw [simpleGraph_restrict_degree,simpleGraph_restrict_degree]
    exact hb
  · intro e he
    obtain ⟨u,v,hne,hev⟩ := Finset.card_eq_two.mp e.property
    have ha := adj_of_edge he (show u∈e.val by rw [hev]; simp)
      (show v∈e.val by rw [hev]; simp) hne
    rw [simpleGraph_restrict] at ha
    have hb := hh.2.2.2 u v ha
    rw [edgeDegree_of_adj _ e u v hne hev]
    rw [simpleGraph_restrict_degree,simpleGraph_restrict_degree]
    exact hb

end RobustMatching.R8BalancedCut
