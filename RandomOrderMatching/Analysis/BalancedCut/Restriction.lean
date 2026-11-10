import RandomOrderMatching.Analysis.BalancedCut.Unfolding
import RandomOrderMatching.Acquisition.GraphDegrees
import RandomOrderMatching.Graph.CoverHosts

/-! Finite edge-set cut restriction, exact degree transport, and benchmark
optimum preservation for the actual graph interfaces used downstream. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RandomOrderMatching.Analysis.BalancedCut
open RandomOrderMatching.Graph RandomOrderMatching.Graph.Konig RandomOrderMatching.Graph.CoverHosts
open RandomOrderMatching.Analysis.BalancedCut.DegreeInterface RandomOrderMatching.Analysis.Profile

variable {X : Type*} [Fintype X] [DecidableEq X]

def cutSide (z : X→Bool) : Finset X := Finset.univ.filter fun v=>z v=true
def restrict (H : Graph X) (z : X→Bool) : Graph X := crossingEdges H (cutSide z)

theorem pair_cross_iff (z : X→Bool) (u v : X) (hne : u≠v) :
    (({u,v}:Finset X) ∩ cutSide z).card=1 ↔ z u≠z v := by
  cases hu : z u <;> cases hv : z v <;> simp [cutSide,hu,hv,hne]

theorem restrict_subset (H : Graph X) (z : X→Bool) : restrict H z⊆H :=
  Finset.filter_subset _ _

theorem simpleGraph_restrict (H : Graph X) (z : X→Bool) :
    simpleGraph (restrict H z)=cutGraph (simpleGraph H) z := by
  ext u v
  constructor
  · intro h
    obtain ⟨⟨e,he,hev⟩,hne⟩ := h
    obtain ⟨heH,heC⟩ := Finset.mem_filter.mp he
    have hpair : e.val={u,v} := by simpa only [Sym2.toFinset_mk_eq] using hev.symm
    rw [hpair] at heC
    exact ⟨⟨⟨e,heH,hev⟩,hne⟩,(pair_cross_iff z u v hne).mp heC⟩
  · rintro ⟨⟨⟨e,he,hev⟩,hne⟩,hz⟩
    have hpair : e.val={u,v} := by simpa only [Sym2.toFinset_mk_eq] using hev.symm
    refine ⟨⟨e,Finset.mem_filter.mpr ⟨he,?_⟩,hev⟩,hne⟩
    rw [hpair]
    exact (pair_cross_iff z u v hne).mpr hz

theorem restrict_crosses (H : Graph X) (z : X→Bool) :
    ∀ e∈restrict H z,∀ u∈e.val,∀ v∈e.val,u≠v→z u≠z v := by
  intro e he u hu v hv hne
  have ha : (simpleGraph (restrict H z)).Adj u v :=
    RandomOrderMatching.Graph.Components.adj_of_edge he hu hv hne
  rw [simpleGraph_restrict] at ha
  exact ha.2

theorem restrict_colorable (H : Graph X) (z : X→Bool) :
    (simpleGraph (restrict H z)).Colorable 2 :=
  colorable_of_cut _ _ (restrict_crosses H z)

theorem restrict_contains_matching {G M : Graph X} (hMG : M⊆G) (z : X→Bool)
    (hz : ∀ e∈M,∀ u∈e.val,∀ v∈e.val,u≠v→z u≠z v) : M⊆restrict G z := by
  intro e he
  obtain ⟨u,v,hne,hev⟩ := Finset.card_eq_two.mp e.property
  refine Finset.mem_filter.mpr ⟨hMG he,?_⟩
  rw [hev]
  apply (pair_cross_iff z u v hne).mpr
  exact hz e he u (by rw [hev]; simp) v (by rw [hev]; simp) hne

theorem restrict_rank_of_optimum {G M : Graph X} (hMG : M⊆G) (hM : Matching M)
    (hopt : M.card=rank G) (z : X→Bool)
    (hz : ∀ e∈M,∀ u∈e.val,∀ v∈e.val,u≠v→z u≠z v) :
    rank (restrict G z)=rank G := by
  apply Nat.le_antisymm (rank_mono (restrict_subset G z))
  rw [←hopt]
  exact matching_card_le_rank (restrict_contains_matching hMG z hz) hM

theorem restrict_weighted_optimum (w : Edge X→ℝ) {G M : Graph X}
    (hMG : M⊆G) (hM : Matching M)
    (hopt : (∑ e∈M,w e)=RandomOrderMatching.Graph.WeightedMatching.opt w G) (z : X→Bool)
    (hz : ∀ e∈M,∀ u∈e.val,∀ v∈e.val,u≠v→z u≠z v) :
    RandomOrderMatching.Graph.WeightedMatching.opt w (restrict G z)=
      RandomOrderMatching.Graph.WeightedMatching.opt w G := by
  open RandomOrderMatching.Graph.WeightedMatching RandomOrderMatching.Packing in
    apply le_antisymm (packingOpt_mono Matching empty_matching w (restrict_subset G z))
  change RandomOrderMatching.Graph.WeightedMatching.opt w G ≤
    RandomOrderMatching.Graph.WeightedMatching.opt w (restrict G z)
  rw [←hopt]
  exact RandomOrderMatching.Packing.weight_le_packingOpt Matching
    RandomOrderMatching.Graph.WeightedMatching.empty_matching w hM (restrict_contains_matching hMG z hz)

theorem incidenceDegree_eq_simpleGraph (H : Graph X) (v : X) :
    incidenceDegree H v=((simpleGraph H).degree v : ℝ) := by
  rw [RandomOrderMatching.Acquisition.simpleGraph_degree,incidenceDegree_eq_card]
  rfl

theorem restricted_incidenceDegree (H : Graph X) (z : X→Bool) (v : X) :
    incidenceDegree (restrict H z) v=((cutGraph (simpleGraph H) z).degree v : ℝ) := by
  rw [incidenceDegree_eq_simpleGraph,simpleGraph_restrict]
  congr 2
  exact Subsingleton.elim _ _

theorem simpleGraph_restrict_degree (H : Graph X) (z : X→Bool) (v : X) :
    ((simpleGraph (restrict H z)).degree v : ℝ) =
      ((cutGraph (simpleGraph H) z).degree v : ℝ) := by
  rw [←incidenceDegree_eq_simpleGraph]
  exact restricted_incidenceDegree H z v

theorem edgeDegree_of_adj (H : Graph X) (e : Edge X) (u v : X)
    (hne : u≠v) (hev : e.val={u,v}) :
    (RandomOrderMatching.Acquisition.edgeDegree H e : ℝ)=
      ((simpleGraph H).degree u : ℝ)+(simpleGraph H).degree v := by
  simp [RandomOrderMatching.Acquisition.edgeDegree,hev,hne,RandomOrderMatching.Acquisition.simpleGraph_degree]

theorem actual_edge_upper (H : Graph X) (β : ℝ)
    (hupper : ∀ e∈H,(RandomOrderMatching.Acquisition.edgeDegree H e : ℝ)≤β) :
    ∀ u v,(simpleGraph H).Adj u v→
      ((simpleGraph H).degree u : ℝ)+(simpleGraph H).degree v≤β := by
  intro u v h
  obtain ⟨⟨e,he,hev⟩,hne⟩ := h
  have hp : e.val={u,v} := by simpa only [Sym2.toFinset_mk_eq] using hev.symm
  rw [←edgeDegree_of_adj H e u v hne hp]
  exact hupper e he

theorem actual_edge_lower (H N : Graph X) (β : ℝ)
    (hlower : ∀ e∈N,β≤(RandomOrderMatching.Acquisition.edgeDegree H e : ℝ)) :
    ∀ u v,(simpleGraph N).Adj u v→
      β≤((simpleGraph H).degree u : ℝ)+(simpleGraph H).degree v := by
  intro u v h
  obtain ⟨⟨e,he,hev⟩,hne⟩ := h
  have hp : e.val={u,v} := by simpa only [Sym2.toFinset_mk_eq] using hev.symm
  rw [←edgeDegree_of_adj H e u v hne hp]
  exact hlower e he

/-- The upper balance window also pays for an available underfull edge
that was not itself retained in the reference. No e-membership premise
is needed. This is the internal-available benchmark-pair interface. -/
theorem arbitrary_edge_upper_from_balance (H A : Graph X) (β : ℝ)
    (hbal : ∀ x, incidenceDegree A x ≤ incidenceDegree H x/2+tolerance*β+1/2)
    (e : Edge X) (hdeg : (RandomOrderMatching.Acquisition.edgeDegree H e : ℝ)≤β) :
    (RandomOrderMatching.Acquisition.edgeDegree A e : ℝ)≤betaCut β := by
  obtain ⟨u,v,hne,hev⟩ := Finset.card_eq_two.mp e.property
  have hu := hbal u
  have hv := hbal v
  simp only [incidenceDegree_eq_simpleGraph] at hu hv
  rw [edgeDegree_of_adj H e u v hne hev] at hdeg
  rw [edgeDegree_of_adj A e u v hne hev]
  unfold betaCut tolerance at *
  linarith

end RandomOrderMatching.Analysis.BalancedCut
