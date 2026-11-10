import RobustMatching.R7GraphComponents

/-! Coverage-preserving maximum extension on actual finite general graphs.
The proof chooses a maximum matching with maximum retained vertex coverage
and switches an actual connected component if coverage is missing. -/

noncomputable section
set_option linter.unusedSectionVars false
open Classical

namespace RobustMatching.R7GraphExchange
open RobustMatching.R2Cut RobustMatching.R7GraphKonig RobustMatching.R7GraphComponents

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every matching has a maximum-cardinality extension in covered vertices.
Edges need not be retained. This works in general, not only bipartite, graphs. -/
theorem exists_maximum_covering (K M : Graph V) (hMK : M ⊆ K) (hM : Matching M) :
    ∃ P ⊆ K, Matching P ∧ P.card = rank K ∧ covered M ⊆ covered P := by
  let choices := K.powerset.filter fun P => Matching P ∧ P.card = rank K
  have hchoices : choices.Nonempty := by
    obtain ⟨P, hPK, hP, hPc⟩ := rank_attained K
    exact ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hPK, hP, hPc⟩⟩
  obtain ⟨P, hPchoice, hmax⟩ := choices.exists_max_image
    (fun P => (covered M ∩ covered P).card) hchoices
  obtain ⟨hPpow, hP, hPc⟩ := Finset.mem_filter.mp hPchoice
  have hPK := Finset.mem_powerset.mp hPpow
  refine ⟨P, hPK, hP, hPc, ?_⟩
  intro v hvM
  by_contra hvP
  let c := (simpleGraph (M ∪ P)).connectedComponentMk v
  let S := componentVertices (M ∪ P) c
  have hvS : v ∈ S := by simp [S, c, componentVertices]
  have hcM : ClosedBlock M S := component_closed_left M P c
  have hcP : ClosedBlock P S := component_closed_right M P c
  let P' := (P \ inside P S) ∪ inside M S
  have hP' : Matching P' := block_splice_matching hP hM hcP
  have hP'K : P' ⊆ K := block_splice_subset hPK hMK S
  have hpatch := patch_card (M := P) (D := inside P S) (S := inside M S)
    (show inside P S ⊆ P from Finset.filter_subset _ _)
    ((outside_covered_disjoint hcP).mono_right (inside_covered_subset M S))
  have hbound := matching_card_le_rank hP'K hP'
  have hPvertices := covered_card (matching_mono hP
    (show inside P S ⊆ P from Finset.filter_subset _ _))
  have hstrict : (covered (inside P S)).card < S.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨inside_covered_subset P S, ?_⟩
    intro hh
    have hv := hh.symm ▸ hvS
    exact hvP (covered_mono (show inside P S ⊆ P from Finset.filter_subset _ _) hv)
  have hconn := component_card_le_edges_add_one (M ∪ P) c
  rw [inside_union] at hconn
  have hu := Finset.card_union_le (inside M S) (inside P S)
  change S.card ≤ (inside M S ∪ inside P S).card + 1 at hconn
  change P'.card + (inside P S).card = P.card + (inside M S).card at hpatch
  have hsame : P'.card = rank K := by omega
  have hcoverage : covered P' = (covered P \ S) ∪ (covered M ∩ S) :=
    covered_block_splice hcP hcM
  have hinc : covered M ∩ covered P ⊆ covered M ∩ covered P' := by
    intro x hx
    obtain ⟨hxM, hxP⟩ := Finset.mem_inter.mp hx
    refine Finset.mem_inter.mpr ⟨hxM, ?_⟩
    rw [hcoverage]
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxM, hxS⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxP, hxS⟩)
  have hvgrow : v ∈ covered M ∩ covered P' := by
    refine Finset.mem_inter.mpr ⟨hvM, ?_⟩
    rw [hcoverage]
    exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvM, hvS⟩)
  have hcardgrow : (covered M ∩ covered P).card < (covered M ∩ covered P').card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    exact ⟨hinc, fun hh => hvP (Finset.mem_inter.mp (hh.symm ▸ hvgrow)).2⟩
  have hP'choice : P' ∈ choices :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hP'K, hP', hsame⟩
  exact (not_lt_of_ge (hmax P' hP'choice)) hcardgrow

end RobustMatching.R7GraphExchange

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphExchange.exists_maximum_covering
