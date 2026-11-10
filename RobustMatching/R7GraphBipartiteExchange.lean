import RobustMatching.R7GraphExchange
import RobustMatching.R2CutTransfer

/-! Bipartite maximum matchings can choose their left and right covered
vertex sets independently. The proof uses actual connected components and
cardinality, avoiding an assumed path decomposition or parity oracle. -/

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RobustMatching.R7GraphBipartiteExchange
open RobustMatching.R2Cut RobustMatching.R7GraphKonig
open RobustMatching.R7GraphComponents RobustMatching.R7GraphExchange

variable {V : Type*} [Fintype V] [DecidableEq V]

def Crosses (A : Graph V) (L : Finset V) : Prop :=
  ∀ e ∈ A, (e.val ∩ L).card = 1

theorem crosses_mono {A B : Graph V} {L : Finset V}
    (h : Crosses A L) (hBA : B ⊆ A) : Crosses B L :=
  fun e he => h e (hBA he)

theorem crosses_compl {A : Graph V} {L : Finset V} (h : Crosses A L) :
    Crosses A (Finset.univ \ L) := by
  intro e he
  have heq : e.val ∩ (Finset.univ \ L) = e.val \ L := by ext v; simp
  rw [heq, Finset.card_sdiff, Finset.inter_comm, h e he, e.property]

theorem covered_side_card {M : Graph V} {L : Finset V}
    (hM : Matching M) (hcross : Crosses M L) :
    (covered M ∩ L).card = M.card := by
  have hd : (M : Set (Edge V)).PairwiseDisjoint (fun e => e.val ∩ L) := by
    intro e he f hf hne
    exact (hM he hf hne).mono Finset.inter_subset_left Finset.inter_subset_left
  rw [covered, Finset.biUnion_inter, Finset.card_biUnion hd]
  calc
    ∑ e ∈ M, (e.val ∩ L).card = ∑ _e ∈ M, 1 :=
      Finset.sum_congr rfl (fun e he => hcross e he)
    _ = M.card := by simp

theorem exists_mem_notMem_of_card_eq_of_ne {A B : Finset V}
    (hc : A.card = B.card) (hne : A ≠ B) : ∃ v ∈ A, v ∉ B := by
  apply Finset.not_subset.mp
  intro hh
  exact hne (Finset.eq_of_subset_of_card_le hh hc.ge)

/-- Two equally sized left/right coverage profiles differing on both sides
would require two vertices outside the second coverage set. -/
theorem side_eq_or_other_eq {U W S L : Finset V}
    (hUS : U ⊆ S)
    (hL : (U ∩ L).card = (W ∩ L).card)
    (hR : (U \ L).card = (W \ L).card)
    (hmiss : (S \ W).card ≤ 1) :
    U ∩ L = W ∩ L ∨ U \ L = W \ L := by
  by_cases hleft : U ∩ L = W ∩ L
  · exact Or.inl hleft
  apply Or.inr
  by_contra hright
  obtain ⟨v, hv, hvnot⟩ := exists_mem_notMem_of_card_eq_of_ne hL hleft
  obtain ⟨w, hw, hwnot⟩ := exists_mem_notMem_of_card_eq_of_ne hR hright
  obtain ⟨hvU, hvL⟩ := Finset.mem_inter.mp hv
  obtain ⟨hwU, hwL⟩ := Finset.mem_sdiff.mp hw
  have hvW : v ∉ W := fun h => hvnot (Finset.mem_inter.mpr ⟨h, hvL⟩)
  have hwW : w ∉ W := fun h => hwnot (Finset.mem_sdiff.mpr ⟨h, hwL⟩)
  have hvS := Finset.mem_sdiff.mpr ⟨hUS hvU, hvW⟩
  have hwS := Finset.mem_sdiff.mpr ⟨hUS hwU, hwW⟩
  have heq := Finset.card_le_one.mp hmiss v hvS w hwS
  exact hwL (heq ▸ hvL)

/-- In one actual union component of two maximum bipartite matchings,
at least one side has identical coverage. -/
theorem component_side_eq_or_other_eq {A P Q : Graph V} {L : Finset V}
    (hPA : P ⊆ A) (hQA : Q ⊆ A) (hP : Matching P) (hQ : Matching Q)
    (hPc : P.card = rank A) (hQc : Q.card = rank A) (hcross : Crosses A L)
    (c : (simpleGraph (P ∪ Q)).ConnectedComponent) :
    let S := componentVertices (P ∪ Q) c
    (covered P ∩ S) ∩ L = (covered Q ∩ S) ∩ L ∨
      (covered P ∩ S) \ L = (covered Q ∩ S) \ L := by
  dsimp only
  let S := componentVertices (P ∪ Q) c
  have hcP : ClosedBlock P S := component_closed_left P Q c
  have hcQ : ClosedBlock Q S := component_closed_right P Q c
  have hsame := (maximum_block_splice hPA hQA hP hQ hPc hQc hcP hcQ).1
  have hPi : Matching (inside P S) := matching_mono hP (Finset.filter_subset _ _)
  have hQi : Matching (inside Q S) := matching_mono hQ (Finset.filter_subset _ _)
  have hPL := covered_side_card hPi (crosses_mono hcross ((Finset.filter_subset _ _).trans hPA))
  have hQL := covered_side_card hQi (crosses_mono hcross ((Finset.filter_subset _ _).trans hQA))
  have hPR := covered_side_card hPi
    (crosses_compl (crosses_mono hcross ((Finset.filter_subset _ _).trans hPA)))
  have hQR := covered_side_card hQi
    (crosses_compl (crosses_mono hcross ((Finset.filter_subset _ _).trans hQA)))
  have hconn := component_card_le_edges_add_one (P ∪ Q) c
  rw [inside_union] at hconn
  have hu := Finset.card_union_le (inside P S) (inside Q S)
  have hQverts := covered_card hQi
  have hQS := inside_covered_subset Q S
  have hd := Finset.card_sdiff_of_subset hQS
  have hmiss : (S \ covered (inside Q S)).card ≤ 1 := by
    change S.card ≤ (inside P S ∪ inside Q S).card + 1 at hconn
    omega
  have hright_eq (T : Finset V) : T ∩ (Finset.univ \ L) = T \ L := by ext v; simp
  rw [hright_eq] at hPR hQR
  have hl : (covered (inside P S) ∩ L).card = (covered (inside Q S) ∩ L).card := by omega
  have hr : (covered (inside P S) \ L).card = (covered (inside Q S) \ L).card := by omega
  have hh := side_eq_or_other_eq (inside_covered_subset P S) hl hr hmiss
  rwa [covered_inside hcP, covered_inside hcQ] at hh

def selectedComponents (G : Graph V)
    (p : (simpleGraph G).ConnectedComponent → Prop) : Finset V :=
  Finset.univ.filter fun v => p ((simpleGraph G).connectedComponentMk v)

theorem selected_components_closed (G : Graph V)
    (p : (simpleGraph G).ConnectedComponent → Prop) :
    ClosedBlock G (selectedComponents G p) := by
  intro e he
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < e.val.card by rw [e.property]; decide)
  have hlabel : ∀ v ∈ e.val,
      (simpleGraph G).connectedComponentMk u = (simpleGraph G).connectedComponentMk v :=
    fun v hv => SimpleGraph.ConnectedComponent.sound (reachable_of_edge he hu hv)
  by_cases hp : p ((simpleGraph G).connectedComponentMk u)
  · apply Or.inl
    intro v hv
    simp only [selectedComponents, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [← hlabel v hv]
  · apply Or.inr
    apply Finset.disjoint_left.mpr
    intro v hv hs
    have hvp : p ((simpleGraph G).connectedComponentMk v) := (Finset.mem_filter.mp hs).2
    exact hp ((hlabel v hv).symm ▸ hvp)

/-- An actual maximum matching can combine the left coverage of one maximum
matching with the right coverage of another. -/
theorem independent_side_coverage {A P Q : Graph V} {L : Finset V}
    (hPA : P ⊆ A) (hQA : Q ⊆ A) (hP : Matching P) (hQ : Matching Q)
    (hPc : P.card = rank A) (hQc : Q.card = rank A) (hcross : Crosses A L) :
    ∃ M ⊆ A, Matching M ∧ M.card = rank A ∧
      covered M ∩ L = covered Q ∩ L ∧
      covered M ∩ (Finset.univ \ L) = covered P ∩ (Finset.univ \ L) := by
  let p : (simpleGraph (P ∪ Q)).ConnectedComponent → Prop := fun c =>
    (covered P ∩ componentVertices (P ∪ Q) c) ∩ L ≠
      (covered Q ∩ componentVertices (P ∪ Q) c) ∩ L
  let S := selectedComponents (P ∪ Q) p
  have hc := selected_components_closed (P ∪ Q) p
  have hcP : ClosedBlock P S := fun e he => hc e (Finset.mem_union_left _ he)
  have hcQ : ClosedBlock Q S := fun e he => hc e (Finset.mem_union_right _ he)
  have hleft : ∀ v ∈ L, v ∉ S → (v ∈ covered P ↔ v ∈ covered Q) := by
    intro v hvL hvS
    have hp : ¬p ((simpleGraph (P ∪ Q)).connectedComponentMk v) := by
      simpa [S, selectedComponents] using hvS
    have heq := not_ne_iff.mp hp
    have hmem := Finset.ext_iff.mp heq v
    simpa [p, componentVertices, hvL] using hmem
  have hright : ∀ v ∈ Finset.univ \ L, v ∈ S → (v ∈ covered P ↔ v ∈ covered Q) := by
    intro v hvR hvS
    have hp : p ((simpleGraph (P ∪ Q)).connectedComponentMk v) := by
      simpa [S, selectedComponents] using hvS
    have hh := component_side_eq_or_other_eq hPA hQA hP hQ hPc hQc hcross
      ((simpleGraph (P ∪ Q)).connectedComponentMk v)
    have hr := hh.resolve_left hp
    have hmem := Finset.ext_iff.mp hr v
    have hvL := (Finset.mem_sdiff.mp hvR).2
    simpa [componentVertices, hvL] using hmem
  obtain ⟨_, hm, hmc⟩ := maximum_block_splice hPA hQA hP hQ hPc hQc hcP hcQ
  obtain ⟨hl, hr⟩ := block_splice_side_coverage hcP hcQ hleft hright
  exact ⟨_, block_splice_subset hPA hQA S, hm, hmc, hl, hr⟩

end RobustMatching.R7GraphBipartiteExchange

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphBipartiteExchange.independent_side_coverage
