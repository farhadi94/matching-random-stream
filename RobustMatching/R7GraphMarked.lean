import RobustMatching.R7GraphCutTransfer
import RobustMatching.R7AlgebraPathValue

/-! Actual bipartite deletion witnesses give an admissible marked matching
pair, with exactly the same total weight. No path decomposition is assumed. -/

noncomputable section
open scoped BigOperators symmDiff
open Classical

namespace RobustMatching.R7GraphMarked
open RobustMatching.R2Cut RobustMatching.R7GraphKonig
open RobustMatching.R7GraphComponents RobustMatching.R7GraphBipartiteExchange
open RobustMatching.R7AlgebraPath

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem simpleGraph_mono {G H : Graph V} (h : G ⊆ H) :
    simpleGraph G ≤ simpleGraph H := by
  intro u v ha
  obtain ⟨⟨e, he, hv⟩, hn⟩ := ha
  exact ⟨⟨e, h he, hv⟩, hn⟩

theorem separated_mono {G H : Graph V} {marks : Finset V}
    (h : G ⊆ H) (hs : Separated H marks) : Separated G marks := by
  intro u hu v hv hr
  exact hs u hu v hv (hr.mono (simpleGraph_mono h))

/-- Connectivity and the two disjoint side coverages leave room for at
most one marked vertex. This proves the parity consequence on actual graphs. -/
theorem cut_component_marks_le_one {A P Q : Graph V} {L IL IR : Finset V}
    (hPA : P ⊆ A) (hQA : Q ⊆ A) (hP : Matching P) (hQ : Matching Q)
    (hcross : Crosses A L) (hIL : IL ⊆ L) (hIR : IR ⊆ Finset.univ \ L)
    (haP : Disjoint (covered P) IL) (haQ : Disjoint (covered Q) IR)
    (c : (simpleGraph (P ∪ Q)).ConnectedComponent) :
    ((IL ∪ IR) ∩ componentVertices (P ∪ Q) c).card ≤ 1 := by
  let S := componentVertices (P ∪ Q) c
  let U := covered (inside P S) ∩ L
  let W := covered (inside Q S) ∩ (Finset.univ \ L)
  have hU : U.card = (inside P S).card := covered_side_card
    (matching_mono hP (Finset.filter_subset _ _))
    (crosses_mono hcross ((Finset.filter_subset _ _).trans hPA))
  have hW : W.card = (inside Q S).card := covered_side_card
    (matching_mono hQ (Finset.filter_subset _ _))
    (crosses_compl (crosses_mono hcross ((Finset.filter_subset _ _).trans hQA)))
  have hd : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro v hu hw
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hw).2).2 (Finset.mem_inter.mp hu).2
  have hsub : U ∪ W ⊆ S := by
    intro v hv
    rcases Finset.mem_union.mp hv with hu | hw
    · exact inside_covered_subset P S (Finset.mem_inter.mp hu).1
    · exact inside_covered_subset Q S (Finset.mem_inter.mp hw).1
  have hmarks : (IL ∪ IR) ∩ S ⊆ S \ (U ∪ W) := by
    intro v hv
    obtain ⟨hm, hs⟩ := Finset.mem_inter.mp hv
    refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
    intro hz
    rcases Finset.mem_union.mp hm with hl | hr <;>
      rcases Finset.mem_union.mp hz with hu | hw
    · exact Finset.disjoint_left.mp haP
        (covered_mono (Finset.filter_subset _ _) (Finset.mem_inter.mp hu).1) hl
    · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hw).2).2 (hIL hl)
    · exact (Finset.mem_sdiff.mp (hIR hr)).2 (Finset.mem_inter.mp hu).2
    · exact Finset.disjoint_left.mp haQ
        (covered_mono (Finset.filter_subset _ _) (Finset.mem_inter.mp hw).1) hr
  have hconn := component_card_le_edges_add_one (P ∪ Q) c
  rw [inside_union] at hconn
  have huc := Finset.card_union_le (inside P S) (inside Q S)
  have hdc := Finset.card_union_of_disjoint hd
  have hsc := Finset.card_sdiff_of_subset hsub
  have hmc := Finset.card_le_card hmarks
  change S.card ≤ (inside P S ∪ inside Q S).card + 1 at hconn
  change ((IL ∪ IR) ∩ S).card ≤ 1
  omega

theorem cut_union_separated {A P Q : Graph V} {L IL IR : Finset V}
    (hPA : P ⊆ A) (hQA : Q ⊆ A) (hP : Matching P) (hQ : Matching Q)
    (hcross : Crosses A L) (hIL : IL ⊆ L) (hIR : IR ⊆ Finset.univ \ L)
    (haP : Disjoint (covered P) IL) (haQ : Disjoint (covered Q) IR) :
    Separated (P ∪ Q) (IL ∪ IR) := by
  intro u hu v hv hr
  let c := (simpleGraph (P ∪ Q)).connectedComponentMk u
  have hcard := cut_component_marks_le_one hPA hQA hP hQ hcross hIL hIR haP haQ c
  have huS : u ∈ componentVertices (P ∪ Q) c := by simp [componentVertices, c]
  have hvS : v ∈ componentVertices (P ∪ Q) c := by
    simpa [componentVertices, c] using (SimpleGraph.ConnectedComponent.sound hr).symm
  exact Finset.card_le_one.mp hcard u (Finset.mem_inter.mpr ⟨hu, huS⟩)
    v (Finset.mem_inter.mpr ⟨hv, hvS⟩)

theorem complementary_splice_weight (w : Edge V → ℝ) (P Q : Graph V) (S : Finset V)
    (hcP : ClosedBlock P S) (hcQ : ClosedBlock Q S) :
    pairWeight w ((Q \ inside Q S) ∪ inside P S, (P \ inside P S) ∪ inside Q S) =
      pairWeight w (P,Q) := by
  have hdP := edges_disjoint_of_covered_disjoint
    ((outside_covered_disjoint hcP).mono_right (inside_covered_subset Q S))
  have hdQ := edges_disjoint_of_covered_disjoint
    ((outside_covered_disjoint hcQ).mono_right (inside_covered_subset P S))
  unfold pairWeight
  rw [Finset.sum_union hdQ, Finset.sum_union hdP]
  have hp := Finset.sum_sdiff (f := w) (show inside P S ⊆ P from Finset.filter_subset _ _)
  have hq := Finset.sum_sdiff (f := w) (show inside Q S ⊆ Q from Finset.filter_subset _ _)
  linarith

/-- Reorient actual union components to avoid all marked vertices in the
first matching, without changing total weight. -/
theorem cut_pair_admissible (w : Edge V → ℝ) {A P Q : Graph V} {L IL IR : Finset V}
    (hPA : P ⊆ A) (hQA : Q ⊆ A) (hP : Matching P) (hQ : Matching Q)
    (hcross : Crosses A L) (hIL : IL ⊆ L) (hIR : IR ⊆ Finset.univ \ L)
    (haP : Disjoint (covered P) IL) (haQ : Disjoint (covered Q) IR) :
    ∃ N₁ ⊆ A, ∃ N₂ ⊆ A, Admissible N₁ N₂ (IL ∪ IR) ∧
      pairWeight w (N₁,N₂) = pairWeight w (P,Q) := by
  have hsep := cut_union_separated hPA hQA hP hQ hcross hIL hIR haP haQ
  let p : (simpleGraph (P ∪ Q)).ConnectedComponent → Prop := fun c =>
    ∃ u ∈ IL, (simpleGraph (P ∪ Q)).connectedComponentMk u = c
  let S := selectedComponents (P ∪ Q) p
  have hc := selected_components_closed (P ∪ Q) p
  have hcP : ClosedBlock P S := fun e he => hc e (Finset.mem_union_left _ he)
  have hcQ : ClosedBlock Q S := fun e he => hc e (Finset.mem_union_right _ he)
  have hILS : IL ⊆ S := by
    intro u hu
    simp only [S, selectedComponents, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u,hu,rfl⟩
  have hSIR : Disjoint S IR := by
    apply Finset.disjoint_left.mpr
    intro v hv hvIR
    have hp : p ((simpleGraph (P ∪ Q)).connectedComponentMk v) := by
      simpa only [S, selectedComponents, Finset.mem_filter, Finset.mem_univ, true_and] using hv
    obtain ⟨u,hu,he⟩ := hp
    have huv := hsep u (Finset.mem_union_left _ hu) v (Finset.mem_union_right _ hvIR)
      (SimpleGraph.ConnectedComponent.exact he)
    exact (Finset.mem_sdiff.mp (hIR hvIR)).2 (huv ▸ hIL hu)
  let N₁ := (Q \ inside Q S) ∪ inside P S
  let N₂ := (P \ inside P S) ∪ inside Q S
  have hn₁ := block_splice_matching hQ hP hcQ
  have hn₂ := block_splice_matching hP hQ hcP
  have havoid : Disjoint (covered N₁) (IL ∪ IR) := by
    rw [show covered N₁ = (covered Q \ S) ∪ (covered P ∩ S) from
      covered_block_splice hcQ hcP]
    apply Finset.disjoint_left.mpr
    intro v hv hm
    rcases Finset.mem_union.mp hv with hq | hp <;>
      rcases Finset.mem_union.mp hm with hl | hr
    · exact (Finset.mem_sdiff.mp hq).2 (hILS hl)
    · exact Finset.disjoint_left.mp haQ (Finset.mem_sdiff.mp hq).1 hr
    · exact Finset.disjoint_left.mp haP (Finset.mem_inter.mp hp).1 hl
    · exact Finset.disjoint_left.mp hSIR (Finset.mem_inter.mp hp).2 hr
  have hnewsub : N₁ ∆ N₂ ⊆ P ∪ Q := by
    intro e he
    have hh : e ∈ N₁ ∨ e ∈ N₂ := Finset.mem_union.mp (Finset.symmDiff_subset_union he)
    rcases hh with hh | hh
    · exact block_splice_subset (Finset.subset_union_right) (Finset.subset_union_left) S hh
    · exact block_splice_subset (Finset.subset_union_left) (Finset.subset_union_right) S hh
  exact ⟨N₁,block_splice_subset hQA hPA S,N₂,block_splice_subset hPA hQA S,
    ⟨hn₁,hn₂,havoid,separated_mono hnewsub hsep⟩,
    complementary_splice_weight w P Q S hcP hcQ⟩

/-- The two actual weighted deletion optima lie below the marked matching-pair
value in any ambient graph. Weights may be arbitrary real numbers. -/
theorem deletion_optima_le_pathValue (w : Edge V → ℝ) {A K : Graph V}
    {L IL IR : Finset V} (hAK : A ⊆ K) (hcross : Crosses A L)
    (hIL : IL ⊆ L) (hIR : IR ⊆ Finset.univ \ L) :
    RobustMatching.R6FableImportance.opt w (deleteVertices A IL) +
      RobustMatching.R6FableImportance.opt w (deleteVertices A IR) ≤
        pathValue w K (IL ∪ IR) := by
  obtain ⟨P,hPD,hP,hPv⟩ := RobustMatching.Lower.packingOpt_attained Matching
    RobustMatching.R6FableImportance.empty_matching w (deleteVertices A IL)
  obtain ⟨Q,hQD,hQ,hQv⟩ := RobustMatching.Lower.packingOpt_attained Matching
    RobustMatching.R6FableImportance.empty_matching w (deleteVertices A IR)
  have hPA : P ⊆ A := hPD.trans (Finset.filter_subset _ _)
  have hQA : Q ⊆ A := hQD.trans (Finset.filter_subset _ _)
  have haP : Disjoint (covered P) IL :=
    RobustMatching.R7GraphCutTransfer.covered_delete_disjoint hPD
  have haQ : Disjoint (covered Q) IR :=
    RobustMatching.R7GraphCutTransfer.covered_delete_disjoint hQD
  obtain ⟨N₁,hN₁,N₂,hN₂,hadm,hwt⟩ :=
    cut_pair_admissible w hPA hQA hP hQ hcross hIL hIR haP haQ
  have hh := pairWeight_le_pathValue w (hN₁.trans hAK) (hN₂.trans hAK) hadm
  rw [hwt] at hh
  simpa only [RobustMatching.R6FableImportance.opt,hPv,hQv,pairWeight] using hh

end RobustMatching.R7GraphMarked

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphMarked.cut_union_separated
#print axioms RobustMatching.R7GraphMarked.cut_pair_admissible
#print axioms RobustMatching.R7GraphMarked.deletion_optima_le_pathValue
