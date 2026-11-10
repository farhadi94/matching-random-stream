import RandomOrderMatching.Graph.Konig.HallDefect
import RandomOrderMatching.Graph.Basic

/-!
Unconditional finite bipartite matching-cover duality, with an attained
matching and cover. The Hall-deficiency foundation is adapted from the CC0
source documented in `RandomOrderMatching.Graph.Konig.Definitions`; the project graph bridge below is
new. No cover or maximum-matching extension witness is assumed.
-/

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RandomOrderMatching.Graph.Konig

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Finite Hall yields an actual matching and an equal-size actual cover. -/
theorem exists_matching_cover (G : SimpleGraph V) (hG : G.Colorable 2) :
    ∃ M : Finset (Sym2 V), ∃ C : Finset V,
      IsMatching G M ∧ IsVertexCover G C ∧ M.card = C.card := by
  obtain ⟨c⟩ := hG
  let A := Finset.univ.filter fun v => c v = 0
  obtain ⟨S, d, hSA, hSd, hd, hmax⟩ := exists_max_defect G A
  obtain ⟨f, hinj, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' _).mp
      (hall_condition_augmented G A d hmax)
  obtain ⟨M, hM, hcard⟩ := exists_matching_from_hall_inj G c A d rfl f hinj hmem
  have hC := isVertexCover_bipartite_defect G c A S rfl hSA
  have heq := bipartite_defect_cover_card G c A S d rfl hSA hd hSd
  exact ⟨M, _, hM, hC, Nat.le_antisymm
    (matching_card_le_vertexCover_card G hM hC) (by omega)⟩

/-- Both extrema are attained; optimality follows from weak duality. -/
theorem exists_optimal_matching_cover (G : SimpleGraph V) (hG : G.Colorable 2) :
    ∃ M : Finset (Sym2 V), ∃ C : Finset V,
      IsMatching G M ∧ IsVertexCover G C ∧ M.card = C.card ∧
      (∀ N, IsMatching G N → N.card ≤ M.card) ∧
      (∀ D, IsVertexCover G D → C.card ≤ D.card) := by
  obtain ⟨M, C, hM, hC, heq⟩ := exists_matching_cover G hG
  exact ⟨M, C, hM, hC, heq,
    fun N hN => heq ▸ matching_card_le_vertexCover_card G hN hC,
    fun D hD => heq ▸ matching_card_le_vertexCover_card G hM hD⟩

open RandomOrderMatching.Graph

/-- The same finite two-vertex-edge graph, viewed as a mathlib simple graph. -/
def simpleGraph (G : Graph V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {q | ∃ e ∈ G, q.toFinset = e.val}

theorem mem_simpleGraph_edge {G : Graph V} {q : Sym2 V}
    (hq : q ∈ (simpleGraph G).edgeSet) :
    ∃ e ∈ G, q.toFinset = e.val := by
  exact (show q ∈ {q | ∃ e ∈ G, q.toFinset = e.val} \ Sym2.diagSet by
    simpa [simpleGraph, SimpleGraph.edgeSet_fromEdgeSet] using hq).1

theorem sym2_toFinset_injective : Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e f h
  apply Sym2.ext
  intro v
  simpa only [Sym2.mem_toFinset] using Finset.ext_iff.mp h v

/-- An actual matching in the simple-graph view maps to an actual project
matching, with unchanged edge count. -/
theorem matching_of_simpleGraph {G : Graph V} {M : Finset (Sym2 V)}
    (hM : IsMatching (simpleGraph G) M) :
    ∃ N : Graph V, N ⊆ G ∧ Matching N ∧ N.card = M.card := by
  let f : M → Edge V := fun q => ⟨q.val.toFinset, by
    obtain ⟨e, _, he⟩ := mem_simpleGraph_edge (hM.1 q.val q.property)
    rw [he]
    exact e.property⟩
  let N := Finset.univ.image f
  have hf : Function.Injective f := by
    intro e g he
    apply Subtype.ext
    exact sym2_toFinset_injective (congrArg Subtype.val he)
  refine ⟨N, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨g, hg, heq⟩ := mem_simpleGraph_edge (hM.1 q.val q.property)
    have hfg : f q = g := Subtype.ext heq
    exact hfg ▸ hg
  · intro e he g hg hne
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hg
    apply Finset.disjoint_left.mpr
    intro v hvq hvr
    have hqr : q.val ≠ r.val := by
      intro hh
      exact hne (congrArg f (Subtype.ext hh))
    exact hM.2 q.val q.property r.val r.property hqr
      ⟨v, Sym2.mem_toFinset.mp hvq, Sym2.mem_toFinset.mp hvr⟩
  · dsimp [N]
    rw [Finset.card_image_of_injective _ hf]
    exact Finset.card_attach

theorem cover_of_simpleGraph {G : Graph V} {C : Finset V}
    (hC : IsVertexCover (simpleGraph G) C) :
    ∀ e ∈ G, (e.val ∩ C).Nonempty := by
  intro e he
  obtain ⟨u, v, huv, heq⟩ := Finset.card_eq_two.mp e.property
  have hadj : (simpleGraph G).Adj u v := by
    refine ⟨?_, huv⟩
    exact ⟨e, he, by simpa only [Sym2.toFinset_mk_eq] using heq.symm⟩
  rcases hC u v hadj with hu | hv
  · exact ⟨u, Finset.mem_inter.mpr ⟨by simp [heq], hu⟩⟩
  · exact ⟨v, Finset.mem_inter.mpr ⟨by simp [heq], hv⟩⟩

/-- Unconditional König theorem for the project's exact finite edge sets. -/
theorem project_konig (G : Graph V) (hG : (simpleGraph G).Colorable 2) :
    ∃ M C, M ⊆ G ∧ Matching M ∧
      (∀ e ∈ G, (e.val ∩ C).Nonempty) ∧ M.card = C.card ∧ C.card = rank G := by
  obtain ⟨N, C, hN, hC, hNC⟩ := exists_matching_cover (simpleGraph G) hG
  obtain ⟨M, hMG, hM, hMN⟩ := matching_of_simpleGraph hN
  have hc := cover_of_simpleGraph hC
  have hMC : M.card = C.card := hMN.trans hNC
  have hupper : rank G ≤ C.card := rank_le fun Q hQG hQ =>
    matching_le_cover hQ (fun e he => hc e (hQG he))
  have hlower := matching_card_le_rank hMG hM
  exact ⟨M, C, hMG, hM, hc, hMC, by omega⟩

end RandomOrderMatching.Graph.Konig

set_option pp.fullNames true
#print axioms RandomOrderMatching.Graph.Konig.exists_matching_cover
#print axioms RandomOrderMatching.Graph.Konig.project_konig
