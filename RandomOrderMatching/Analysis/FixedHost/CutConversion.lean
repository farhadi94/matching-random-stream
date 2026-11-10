import RandomOrderMatching.Analysis.FixedHost.BalancedGeometry
import RandomOrderMatching.Phases.Embedding.CanonicalCopies

noncomputable section
set_option linter.unusedSectionVars false
open Classical
namespace RandomOrderMatching.Analysis.FixedHost
open RandomOrderMatching.Graph RandomOrderMatching.Analysis.BalancedCut RandomOrderMatching.Analysis.BalancedCut.DegreeInterface RandomOrderMatching.Phases.Embedding RandomOrderMatching.Graph.BipartiteExchange
open RandomOrderMatching.Analysis.Profile RandomOrderMatching.Graph.Konig RandomOrderMatching.Acquisition
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem copyCut_cutSide (z : V→Bool) (W : ℕ) :
    copyCut (cutSide z) W=cutSide (fun x:V×Fin W=>z x.1) := by
  ext x
  simp [copyCut,cutSide]

theorem restricted_crosses_copyCut (H : Graph (V×Fin W)) (z : V→Bool) :
    Crosses (restrict H (fun x=>z x.1)) (copyCut (cutSide z) W) := by
  rw [copyCut_cutSide]
  intro e he
  exact (Finset.mem_filter.mp he).2

theorem side_crosses_copyCut (H : Graph (V×Fin W)) (z : V→Bool)
    (hz : ∀e∈H,∀u∈e.val,∀v∈e.val,u≠v→z u.1≠z v.1) :
    Crosses H (copyCut (cutSide z) W) := by
  rw [copyCut_cutSide]
  intro e he
  obtain ⟨u,v,hne,hev⟩ := Finset.card_eq_two.mp e.property
  rw [hev]
  apply (pair_cross_iff (fun x:V×Fin W=>z x.1) u v hne).mpr
  exact hz e he u (by rw [hev]; simp) v (by rw [hev]; simp) hne

/-- Only the actually retained copied support is used. The complete
original graph is an analytic ambient graph for the balanced-cut lemma. -/
theorem consistent_subgraph_unfolding {W : ℕ} (w : Edge V→ℕ)
    (parent : Edge (V×Fin W)→Edge V) (H : Graph (V×Fin W))
    (hc : ConsistentCopies W w parent H) :
    simpleGraph H≤unfolding (simpleGraph (Finset.univ:Graph V)) (canonicalSymWeight w) W := by
  intro x y hxy
  obtain ⟨⟨f,hf,hev⟩,hne⟩ := hxy
  have hp : f.val={x,y} := by simpa only [Sym2.toFinset_mk_eq] using hev.symm
  have hproj : ({x.1,y.1}:Finset V)=(parent f).val := by
    have hh := hc.projection f hf
    simpa only [hp,Finset.image_insert,Finset.image_singleton] using hh
  have hno : x.1≠y.1 := by
    intro hh
    have hcard := congrArg Finset.card hproj
    simp [hh,(parent f).property] at hcard
  have hs : s(x.1,y.1)=canonicalEdgeSym (parent f) := by
    apply sym2_toFinset_injective
    simpa only [Sym2.toFinset_mk_eq,canonicalEdgeSym_toFinset] using hproj
  constructor
  · exact ⟨⟨parent f,Finset.mem_univ _,by simpa only [Sym2.toFinset_mk_eq] using hproj⟩,hno⟩
  · rw [hs,canonicalSymWeight_edge]
    exact hc.index f hf x (by rw [hp]; simp) y (by rw [hp]; simp) hne

theorem final_scale_positive (W L : ℕ) (hW : 1≤W) (hL : 1≤L) :
    0<betaCut (beta0 W L) ∧ 10^30*(W:ℝ)*L/2≤betaCut (beta0 W L) := by
  have h0 := beta0_large W L hW hL
  unfold betaCut beta0 at *
  constructor <;> nlinarith

theorem final_log_scale {N δ : ℝ} {L : ℕ} (hN : 0<N) (hδ : 0<δ)
    (hlog : Real.log (100*N/δ)≤L) :
    Real.exp (-(L:ℝ))≤(δ/100)/N := by
  have hp : 0<100*N/δ := by positivity
  have h := Real.exp_le_exp.mpr (neg_le_neg hlog)
  calc
    _ ≤ Real.exp (-Real.log (100*N/δ)) := h
    _ = _ := by rw [Real.exp_neg,Real.exp_log hp]; field_simp

end RandomOrderMatching.Analysis.FixedHost
