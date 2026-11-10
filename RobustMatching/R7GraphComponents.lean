import RobustMatching.R7GraphKonig
import RobustMatching.R2CutExchange
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Actual connected-component blocks of finite matching unions. The
component cardinality bound comes from the spanning-tree inequality, not
an assumed alternating-path decomposition. -/

noncomputable section
set_option linter.unusedSectionVars false
open Classical

namespace RobustMatching.R7GraphComponents
open RobustMatching.R2Cut RobustMatching.R7GraphKonig

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edge_eq_pair {e : Edge V} {u v : V} (hu : u ∈ e.val)
    (hv : v ∈ e.val) (hne : u ≠ v) : e.val = {u, v} := by
  apply (Finset.eq_of_subset_of_card_le (show {u, v} ⊆ e.val by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption) ?_).symm
  rw [e.property, Finset.card_pair hne]

theorem adj_of_edge {G : Graph V} {e : Edge V} (he : e ∈ G)
    {u v : V} (hu : u ∈ e.val) (hv : v ∈ e.val) (hne : u ≠ v) :
    (simpleGraph G).Adj u v := by
  refine ⟨⟨e, he, ?_⟩, hne⟩
  rw [Sym2.toFinset_mk_eq, edge_eq_pair hu hv hne]

theorem reachable_of_edge {G : Graph V} {e : Edge V} (he : e ∈ G)
    {u v : V} (hu : u ∈ e.val) (hv : v ∈ e.val) :
    (simpleGraph G).Reachable u v := by
  by_cases h : u = v
  · subst v; exact .rfl
  · exact (adj_of_edge he hu hv h).reachable

def componentVertices (G : Graph V) (c : (simpleGraph G).ConnectedComponent) : Finset V :=
  c.supp.toFinset

theorem component_closed (G : Graph V) (c : (simpleGraph G).ConnectedComponent) :
    ClosedBlock G (componentVertices G c) := by
  intro e he
  by_cases h : (e.val ∩ componentVertices G c).Nonempty
  · obtain ⟨u, hu⟩ := h
    refine Or.inl (fun v hv => ?_)
    have huc : (simpleGraph G).connectedComponentMk u = c := by
      simpa [componentVertices] using (Finset.mem_inter.mp hu).2
    have heq := SimpleGraph.ConnectedComponent.sound
      (reachable_of_edge he (Finset.mem_inter.mp hu).1 hv)
    have hvc := heq.symm.trans huc
    simpa [componentVertices] using hvc
  · exact Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp h))

theorem component_connected (G : Graph V) (c : (simpleGraph G).ConnectedComponent) :
    ((simpleGraph G).induce (componentVertices G c : Set V)).Connected := by
  have heq : (componentVertices G c : Set V) = c.supp := by
    ext v
    simp [componentVertices]
  rw [heq]
  exact c.connected_toSimpleGraph

/-- Exact induced-edge count in the project's representation. -/
theorem inside_card_eq_induced (G : Graph V) (S : Finset V) :
    (inside G S).card = ((simpleGraph G).induce (S : Set V)).edgeFinset.card := by
  classical
  rw [← SimpleGraph.card_filter_edgeFinset_toFinset_subset]
  symm
  let Q := (simpleGraph G).edgeFinset.filter fun q => q.toFinset ⊆ S
  let f (q : Sym2 V) (hq : q ∈ Q) : Edge V := ⟨q.toFinset, by
    obtain ⟨e, _, he⟩ := mem_simpleGraph_edge
      ((simpleGraph G).mem_edgeFinset.mp (Finset.mem_filter.mp hq).1)
    rw [he]; exact e.property⟩
  apply Finset.card_bij f
  · intro q hq
    obtain ⟨e, he, heq⟩ := mem_simpleGraph_edge
      ((simpleGraph G).mem_edgeFinset.mp (Finset.mem_filter.mp hq).1)
    have hfe : f q hq = e := Subtype.ext heq
    exact Finset.mem_filter.mpr ⟨hfe ▸ he, (Finset.mem_filter.mp hq).2⟩
  · intro q hq r hr heq
    exact sym2_toFinset_injective (congrArg Subtype.val heq)
  · intro e he
    obtain ⟨heG, heS⟩ := Finset.mem_filter.mp he
    obtain ⟨u, v, huv, heq⟩ := Finset.card_eq_two.mp e.property
    have hqG : s(u, v) ∈ (simpleGraph G).edgeFinset := by
      apply (simpleGraph G).mem_edgeFinset.mpr
      exact ⟨⟨e, heG, by simpa only [Sym2.toFinset_mk_eq] using heq.symm⟩, huv⟩
    have hq : s(u, v) ∈ Q := Finset.mem_filter.mpr ⟨hqG, by
      simpa only [Sym2.toFinset_mk_eq, ← heq] using heS⟩
    exact ⟨s(u, v), hq, Subtype.ext (by simp only [f, Sym2.toFinset_mk_eq, ← heq])⟩

/-- A genuine connected component has at most one more vertex than edges. -/
theorem component_card_le_edges_add_one (G : Graph V)
    (c : (simpleGraph G).ConnectedComponent) :
    (componentVertices G c).card ≤ (inside G (componentVertices G c)).card + 1 := by
  have h := (component_connected G c).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card, ← inside_card_eq_induced] at h
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using h

theorem inside_union (M N : Graph V) (S : Finset V) :
    inside (M ∪ N) S = inside M S ∪ inside N S := by
  ext e
  simp [inside, or_and_right]

theorem component_closed_left (M N : Graph V)
    (c : (simpleGraph (M ∪ N)).ConnectedComponent) :
    ClosedBlock M (componentVertices (M ∪ N) c) :=
  fun e he => component_closed (M ∪ N) c e (Finset.mem_union_left _ he)

theorem component_closed_right (M N : Graph V)
    (c : (simpleGraph (M ∪ N)).ConnectedComponent) :
    ClosedBlock N (componentVertices (M ∪ N) c) :=
  fun e he => component_closed (M ∪ N) c e (Finset.mem_union_right _ he)

/-- Each matching has at most one more edge than the other in a component.
This is derived from connectivity and matching cardinality, not assumed. -/
theorem component_matching_balance (M N : Graph V) (hM : Matching M) (hN : Matching N)
    (c : (simpleGraph (M ∪ N)).ConnectedComponent) :
    (inside M (componentVertices (M ∪ N) c)).card ≤
      (inside N (componentVertices (M ∪ N) c)).card + 1 := by
  let S := componentVertices (M ∪ N) c
  have hconn := component_card_le_edges_add_one (M ∪ N) c
  rw [inside_union] at hconn
  have hunion := Finset.card_union_le (inside M S) (inside N S)
  have hMc := covered_card (matching_mono hM
    (show inside M S ⊆ M from Finset.filter_subset _ _))
  have hv := Finset.card_le_card (inside_covered_subset M S)
  change (covered (inside M S)).card = 2 * (inside M S).card at hMc
  change S.card ≤ (inside M S ∪ inside N S).card + 1 at hconn
  change (inside M S).card ≤ (inside N S).card + 1
  omega

/-- At most two vertices of an actual component are exposed by either
specified matching. No path decomposition or endpoint set is supplied. -/
theorem component_exposed_card_le_two (M N : Graph V) (hM : Matching M) (hN : Matching N)
    (c : (simpleGraph (M ∪ N)).ConnectedComponent) :
    (componentVertices (M ∪ N) c \ covered N).card ≤ 2 := by
  let S := componentVertices (M ∪ N) c
  have hconn := component_card_le_edges_add_one (M ∪ N) c
  rw [inside_union] at hconn
  have hu := Finset.card_union_le (inside M S) (inside N S)
  have hb := component_matching_balance M N hM hN c
  have hn := covered_card (matching_mono hN
    (show inside N S ⊆ N from Finset.filter_subset _ _))
  have hnS := inside_covered_subset N S
  have hnc := covered_inside (component_closed_right M N c)
  have hd := Finset.card_sdiff_of_subset hnS
  have heq : S \ covered N = S \ covered (inside N S) := by
    rw [hnc]
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  change S.card ≤ (inside M S ∪ inside N S).card + 1 at hconn
  change (inside M S).card ≤ (inside N S).card + 1 at hb
  change (covered (inside N S)).card = 2 * (inside N S).card at hn
  change (S \ covered N).card ≤ 2
  rw [heq]
  omega

end RobustMatching.R7GraphComponents

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphComponents.component_exposed_card_le_two
