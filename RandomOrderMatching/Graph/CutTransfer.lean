import RandomOrderMatching.Graph.BipartiteExchange

/-! The complete unweighted cut-transfer inequality on actual finite graphs.
The ambient graph can be nonbipartite and closed proposed edges may already
belong to it. All matching-existence interfaces are proved, not assumed. -/

noncomputable section
set_option linter.unusedSectionVars false
open Classical

namespace RandomOrderMatching.Graph.CutTransfer
open RandomOrderMatching.Graph RandomOrderMatching.Graph.Konig
open RandomOrderMatching.Graph.CoverageExtension RandomOrderMatching.Graph.BipartiteExchange

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem covered_delete_disjoint {A Q : Graph V} {I : Finset V}
    (hQ : Q ⊆ A.filter fun e => Disjoint e.val I) : Disjoint (covered Q) I := by
  apply Finset.disjoint_left.mpr
  intro v hv hi
  obtain ⟨e, he, hve⟩ := mem_covered.mp hv
  exact Finset.disjoint_left.mp (Finset.mem_filter.mp (hQ he)).2 hve hi

/-- There is a maximum matching minimizing covered vertices in a specified
subset of one side; its deletion cost is exactly the rank drop. -/
theorem exists_minimum_side_coverage (A : Graph V) (L I : Finset V)
    (hcross : Crosses A L) (hIL : I ⊆ L) :
    ∃ P ⊆ A, Matching P ∧ P.card = rank A ∧
      (covered P ∩ I).card + rank (A.filter fun e => Disjoint e.val I) = rank A := by
  let D := A.filter fun e => Disjoint e.val I
  obtain ⟨Q, hQD, hQ, hQc⟩ := rank_attained D
  have hQA : Q ⊆ A := hQD.trans (Finset.filter_subset _ _)
  obtain ⟨P, hPA, hP, hPc, hcov⟩ := exists_maximum_covering A Q hQA hQ
  have hPL := covered_side_card hP (crosses_mono hcross hPA)
  have hQL := covered_side_card hQ (crosses_mono hcross hQA)
  have havoid : Disjoint (covered Q) I := covered_delete_disjoint hQD
  have hdis : Disjoint (covered Q ∩ L) (covered P ∩ I) :=
    havoid.mono Finset.inter_subset_left Finset.inter_subset_right
  have hsub : (covered Q ∩ L) ∪ (covered P ∩ I) ⊆ covered P ∩ L := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact Finset.mem_inter.mpr ⟨hcov (Finset.mem_inter.mp h).1, (Finset.mem_inter.mp h).2⟩
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1, hIL (Finset.mem_inter.mp h).2⟩
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hPL, hQL, hPc] at hcount
  have hone : ∀ e ∈ P, (e.val ∩ I).card ≤ 1 := by
    intro e he
    calc
      (e.val ∩ I).card ≤ (e.val ∩ L).card :=
        Finset.card_le_card (Finset.inter_subset_inter_left hIL)
      _ = 1 := hcross e (hPA he)
  have hid := matching_deletion_identity hP hone
  have hdel : P.filter (fun e => Disjoint e.val I) ⊆ D := by
    intro e he
    exact Finset.mem_filter.mpr ⟨hPA (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  have hdelrank := rank_mono hdel
  refine ⟨P, hPA, hP, hPc, ?_⟩
  change (covered P ∩ I).card + rank D = rank A
  omega

/-- The same maximum matching realizes both one-sided deletion rank drops. -/
theorem exists_joint_minimum_coverage (A : Graph V) (L IL IR : Finset V)
    (hcross : Crosses A L) (hIL : IL ⊆ L) (hIR : IR ⊆ Finset.univ \ L) :
    ∃ M ⊆ A, Matching M ∧ M.card = rank A ∧
      (covered M ∩ IL).card + rank (A.filter fun e => Disjoint e.val IL) = rank A ∧
      (covered M ∩ IR).card + rank (A.filter fun e => Disjoint e.val IR) = rank A := by
  obtain ⟨Q, hQA, hQ, hQc, hQL⟩ := exists_minimum_side_coverage A L IL hcross hIL
  obtain ⟨P, hPA, hP, hPc, hPR⟩ :=
    exists_minimum_side_coverage A (Finset.univ \ L) IR (crosses_compl hcross) hIR
  obtain ⟨M, hMA, hM, hMc, hML, hMR⟩ :=
    independent_side_coverage hPA hQA hP hQ hPc hQc hcross
  have hleft : covered M ∩ IL = covered Q ∩ IL := by
    have hh := congrArg (fun T : Finset V => T ∩ IL) hML
    simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr hIL] using hh
  have hright : covered M ∩ IR = covered P ∩ IR := by
    have hh := congrArg (fun T : Finset V => T ∩ IR) hMR
    simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr hIR] using hh
  exact ⟨M, hMA, hM, hMc, hleft ▸ hQL, hright ▸ hPR⟩

/-- Full cut transfer, including proposals already present in the ambient
graph. Only actual graph bipartiteness and singleton closure are assumed. -/
theorem cut_transfer (A K J : Graph V) (L IL IR : Finset V)
    (hAK : A ⊆ K) (hcross : Crosses A L)
    (hIL : IL ⊆ L) (hIR : IR ⊆ Finset.univ \ L)
    (hJ : Matching J) (hends : covered J ⊆ IL ∪ IR)
    (hclosed : ∀ e ∈ J, rank (insert e K) = rank K) :
    rank (A.filter fun e => Disjoint e.val IL) +
      rank (A.filter fun e => Disjoint e.val IR) + J.card ≤ 2 * rank K := by
  obtain ⟨M, hMA, hM, hMc, hleft, hright⟩ :=
    exists_joint_minimum_coverage A L IL IR hcross hIL hIR
  obtain ⟨P, hPK, hP, hPc, hcov⟩ := exists_maximum_covering K M (hMA.trans hAK) hM
  exact cut_transfer_of_matching_witnesses hJ hM hMc hPK hP hPc hcov
    hends hleft hright hclosed

end RandomOrderMatching.Graph.CutTransfer

set_option pp.fullNames true
#print axioms RandomOrderMatching.Graph.CutTransfer.cut_transfer
