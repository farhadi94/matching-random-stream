import RobustMatching.R7GraphCutTransfer

/-! Maximum gate matchings can be chosen with distinct stored root hosts
for every ungated cover vertex. This is a structural graph theorem only. -/

noncomputable section
open scoped BigOperators
open Classical

namespace RobustMatching.R7GraphHosts
open RobustMatching.R2Cut RobustMatching.R7GraphKonig
open RobustMatching.R7GraphExchange RobustMatching.R7GraphBipartiteExchange

variable {V : Type*} [Fintype V] [DecidableEq V]

def crossingEdges (B : Graph V) (C : Finset V) : Graph V :=
  B.filter fun e => (e.val ∩ C).card = 1

theorem matching_crosses_equal_cover {M : Graph V} {C : Finset V}
    (hM : Matching M) (hC : ∀ e ∈ M, (e.val ∩ C).Nonempty) (heq : M.card = C.card) :
    Crosses M C ∧ covered M ∩ C = C := by
  have hd : (M : Set (Edge V)).PairwiseDisjoint (fun e => e.val ∩ C) := by
    intro e he f hf hne
    exact (hM he hf hne).mono Finset.inter_subset_left Finset.inter_subset_left
  have hs : (covered M ∩ C).card = ∑ e ∈ M, (e.val ∩ C).card := by
    rw [covered, Finset.biUnion_inter, Finset.card_biUnion hd]
  have hl : ∀ e ∈ M, 1 ≤ (e.val ∩ C).card :=
    fun e he => Finset.card_pos.mpr (hC e he)
  have hsum : (∑ _e ∈ M, 1) = ∑ e ∈ M, (e.val ∩ C).card := by
    apply le_antisymm
    · exact Finset.sum_le_sum hl
    · rw [← hs]
      simpa [heq] using Finset.card_le_card (Finset.inter_subset_right : covered M ∩ C ⊆ C)
  have hterm := (Finset.sum_eq_sum_iff_of_le hl).mp hsum
  have hcov : covered M ∩ C = C := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    rw [hs, ← hsum]
    simp [heq]
  exact ⟨fun e he => (hterm e he).symm, hcov⟩

/-- Removing cover-internal edges retains a matching saturating a minimum
cover of a bipartite graph. Minimum-cover optimality is the only premise. -/
theorem minimum_cover_crossing_rank (B : Graph V) (C : Finset V)
    (hB : (simpleGraph B).Colorable 2)
    (hC : ∀ e ∈ B, (e.val ∩ C).Nonempty)
    (hmin : ∀ D : Finset V, (∀ e ∈ B, (e.val ∩ D).Nonempty) → C.card ≤ D.card) :
    rank (crossingEdges B C) = C.card := by
  obtain ⟨M,D,hMB,hM,hD,hMD,hDr⟩ := project_konig B hB
  have hle := matching_le_cover hM (fun e he => hC e (hMB he))
  have hge := hmin D hD
  have hMC : M.card = C.card := by omega
  have hc := (matching_crosses_equal_cover hM (fun e he => hC e (hMB he)) hMC).1
  have hsub : M ⊆ crossingEdges B C :=
    fun e he => Finset.mem_filter.mpr ⟨hMB he,hc e he⟩
  have hl := matching_card_le_rank hsub hM
  have hu := rank_mono (show crossingEdges B C ⊆ B from Finset.filter_subset _ _)
  omega

theorem one_side_deleted_coverage {B : Graph V} {C S : Finset V}
    (hcross : Crosses B C) (hS : S ⊆ Finset.univ \ C) :
    covered (B.filter fun e => Disjoint e.val S) ∩ (Finset.univ \ C) =
      (covered B ∩ (Finset.univ \ C)) \ S := by
  ext v
  constructor
  · intro hv
    obtain ⟨hecov,hvR⟩ := Finset.mem_inter.mp hv
    obtain ⟨e,he,hve⟩ := mem_covered.mp hecov
    obtain ⟨heB,hd⟩ := Finset.mem_filter.mp he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr
      ⟨mem_covered.mpr ⟨e,heB,hve⟩,hvR⟩,
      fun hvS => Finset.disjoint_left.mp hd hve hvS⟩
  · intro hv
    obtain ⟨hcov,hvS⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hcov,hvR⟩ := Finset.mem_inter.mp hcov
    obtain ⟨e,he,hve⟩ := mem_covered.mp hcov
    refine Finset.mem_inter.mpr ⟨mem_covered.mpr ⟨e,?_,hve⟩,hvR⟩
    refine Finset.mem_filter.mpr ⟨he,Finset.disjoint_left.mpr ?_⟩
    intro u hue huS
    have hc := crosses_compl hcross e he
    have huv := Finset.card_le_one.mp hc.le u (Finset.mem_inter.mpr ⟨hue,hS huS⟩)
      v (Finset.mem_inter.mpr ⟨hve,hvR⟩)
    exact hvS (huv ▸ huS)

/-- A maximum nonroot gate matching can be chosen so that all ungated
centers are matched to distinct roots by additional stored edges. -/
theorem maximum_gates_with_hosts (B : Graph V) (C S : Finset V)
    (hcross : Crosses B C) (hfull : rank B = C.card)
    (hS : S ⊆ Finset.univ \ C) :
    ∃ Γ H : Graph V,
      Γ ⊆ B.filter (fun e => Disjoint e.val S) ∧ Matching Γ ∧
      Γ.card = rank (B.filter fun e => Disjoint e.val S) ∧
      H ⊆ B ∧ Matching (Γ ∪ H) ∧ Disjoint Γ H ∧
      covered H ∩ C = C \ covered Γ ∧
      (∀ e ∈ H, (e.val ∩ S).card = 1) := by
  let D := B.filter fun e => Disjoint e.val S
  obtain ⟨Q,hQD,hQ,hQc⟩ := rank_attained D
  have hQB : Q ⊆ B := hQD.trans (Finset.filter_subset _ _)
  obtain ⟨P,hPB,hP,hPc,hcov⟩ := exists_maximum_covering B Q hQB hQ
  let Γ := P.filter fun e => Disjoint e.val S
  let H := P \ Γ
  have hΓP : Γ ⊆ P := Finset.filter_subset _ _
  have hΓD : Γ ⊆ D := by
    intro e he
    exact Finset.mem_filter.mpr ⟨hPB (Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩
  have hΓ := matching_mono hP hΓP
  have hQP : covered Q ∩ (Finset.univ \ C) ⊆ covered Γ ∩ (Finset.univ \ C) := by
    rw [one_side_deleted_coverage (crosses_mono hcross hPB) hS]
    intro v hv
    obtain ⟨hvQ,hvR⟩ := Finset.mem_inter.mp hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hcov hvQ,hvR⟩, ?_⟩
    intro hvS
    exact Finset.disjoint_left.mp
      (RobustMatching.R7GraphCutTransfer.covered_delete_disjoint hQD) hvQ hvS
  have hQside := covered_side_card hQ (crosses_compl (crosses_mono hcross hQB))
  have hΓside := covered_side_card hΓ (crosses_compl (crosses_mono hcross (hΓP.trans hPB)))
  have hΓlower := Finset.card_le_card hQP
  have hΓupper := matching_card_le_rank hΓD hΓ
  have hΓcard : Γ.card = rank D := by omega
  have hCovP : covered P ∩ C = C :=
    (matching_crosses_equal_cover hP
      (fun e he => Finset.card_pos.mp (by rw [hcross e (hPB he)]; decide))
      (hPc.trans hfull)).2
  have hpart : Γ ∪ H = P := Finset.union_sdiff_of_subset hΓP
  have hcovpart : covered Γ ∪ covered H = covered P := by rw [← covered_union, hpart]
  have hdiscov : Disjoint (covered H) (covered Γ) := covered_sdiff_disjoint hP hΓP
  have hhostcov : covered H ∩ C = C \ covered Γ := by
    ext v
    constructor
    · intro hv
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).2,
        fun hg => Finset.disjoint_left.mp hdiscov (Finset.mem_inter.mp hv).1 hg⟩
    · intro hv
      obtain ⟨hvC,hvΓ⟩ := Finset.mem_sdiff.mp hv
      have hvP : v ∈ covered P :=
        (Finset.mem_inter.mp (show v ∈ covered P ∩ C from hCovP.symm ▸ hvC)).1
      rw [← hcovpart] at hvP
      exact Finset.mem_inter.mpr ⟨(Finset.mem_union.mp hvP).resolve_left hvΓ,hvC⟩
  have hhostedge : ∀ e ∈ H, (e.val ∩ S).card = 1 := by
    intro e he
    obtain ⟨heP,heΓ⟩ := Finset.mem_sdiff.mp he
    have hn : ¬Disjoint e.val S := by
      intro hd
      exact heΓ (Finset.mem_filter.mpr ⟨heP,hd⟩)
    have hpos : 0 < (e.val ∩ S).card := Finset.card_pos.mpr
      (Finset.not_disjoint_iff_nonempty_inter.mp hn)
    have hle : (e.val ∩ S).card ≤ 1 := by
      have hh := Finset.card_le_card (Finset.inter_subset_inter_left hS :
        e.val ∩ S ⊆ e.val ∩ (Finset.univ \ C))
      rwa [crosses_compl hcross e (hPB heP)] at hh
    omega
  exact ⟨Γ,H,hΓD,hΓ,hΓcard,(Finset.sdiff_subset.trans hPB),
    hpart.symm ▸ hP,edges_disjoint_of_covered_disjoint hdiscov.symm,hhostcov,hhostedge⟩

end RobustMatching.R7GraphHosts

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphHosts.minimum_cover_crossing_rank
#print axioms RobustMatching.R7GraphHosts.maximum_gates_with_hosts
