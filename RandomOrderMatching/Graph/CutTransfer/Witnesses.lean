import RandomOrderMatching.Graph.MatchingExchange

/-!
The final cut-transfer injection is checked on actual matching witnesses.
The theorem `cut_transfer_of_matching_witnesses` has explicit existence-boundary
premises: the minimum-coverage A matching and its coverage-preserving maximum
K extension. This module does NOT claim the full unrestricted cut-transfer
theorem without those premises. Its written proof appears in work/cut/REPORT.md.
-/
noncomputable section
namespace RandomOrderMatching.Graph
variable {V : Type*} [DecidableEq V]

/-- Charge each singleton-closed matching edge to an old covered endpoint or
a newly covered vertex of the supplied maximum matching. -/
theorem closed_matching_charge {K J M P : Graph V}
    {IL IR : Finset V} (hJ : Matching J) (hM : Matching M)
    (hPK : P ⊆ K) (hP : Matching P) (hPc : P.card = rank K)
    (hcov : covered M ⊆ covered P)
    (hends : covered J ⊆ IL ∪ IR)
    (hc : ∀ e ∈ J, rank (insert e K) = rank K) :
    J.card + 2 * M.card ≤
      (covered M ∩ IL).card + (covered M ∩ IR).card + 2 * rank K := by
  let C := (covered M ∩ IL) ∪ (covered M ∩ IR) ∪ (covered P \ covered M)
  have hcover : ∀ e ∈ J, (e.val ∩ C).Nonempty := by
    intro e he
    obtain ⟨v, hv⟩ := closed_edge_meets_maximum hPK hP hPc (hc e he)
    obtain ⟨hve, hvP⟩ := Finset.mem_inter.mp hv
    refine ⟨v, Finset.mem_inter.mpr ⟨hve, ?_⟩⟩
    by_cases hvM : v ∈ covered M
    · have hvJ : v ∈ covered J := mem_covered.mpr ⟨e, he, hve⟩
      rcases Finset.mem_union.mp (hends hvJ) with hvL | hvR
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvM, hvL⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvM, hvR⟩))
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvP, hvM⟩)
  have hj := matching_le_cover hJ hcover
  have hc1 := Finset.card_union_le (covered M ∩ IL) (covered M ∩ IR)
  have hc2 := Finset.card_union_le ((covered M ∩ IL) ∪ (covered M ∩ IR))
    (covered P \ covered M)
  have hnew := Finset.card_sdiff_of_subset hcov
  have hle := Finset.card_le_card hcov
  have hmcard := covered_card hM
  have hpcard := covered_card hP
  dsimp only [C] at hj
  omega

/-- Exact graph-level final implication of cut transfer, with the two
unformalized matching-existence interfaces made visible in the hypotheses. -/
theorem cut_transfer_of_matching_witnesses {A K J M P : Graph V}
    {IL IR : Finset V} (hJ : Matching J) (hM : Matching M)
    (hMc : M.card = rank A)
    (hPK : P ⊆ K) (hP : Matching P) (hPc : P.card = rank K)
    (hcov : covered M ⊆ covered P)
    (hends : covered J ⊆ IL ∪ IR)
    (hleft : (covered M ∩ IL).card + rank (A.filter fun e => Disjoint e.val IL) = rank A)
    (hright : (covered M ∩ IR).card + rank (A.filter fun e => Disjoint e.val IR) = rank A)
    (hc : ∀ e ∈ J, rank (insert e K) = rank K) :
    rank (A.filter fun e => Disjoint e.val IL) +
      rank (A.filter fun e => Disjoint e.val IR) + J.card ≤ 2 * rank K := by
  have hh := closed_matching_charge hJ hM hPK hP hPc hcov hends hc
  omega

theorem rank_of_matching {M : Graph V} (hM : Matching M) : rank M = M.card := by
  apply Nat.le_antisymm
  · exact rank_le (fun N hNM _ => Finset.card_le_card hNM)
  · exact matching_card_le_rank (Finset.Subset.refl _) hM

/-- Deleting vertices from one side of a matching costs exactly its number
of covered vertices on that side. The one-endpoint condition is essential. -/
theorem matching_deletion_identity {M : Graph V} {S : Finset V}
    (hM : Matching M) (hone : ∀ e ∈ M, (e.val ∩ S).card ≤ 1) :
    (covered M ∩ S).card + rank (M.filter fun e => Disjoint e.val S) = M.card := by
  rw [rank_of_matching (matching_mono hM (Finset.filter_subset _ _))]
  have hd : (M : Set (Edge V)).PairwiseDisjoint (fun e => e.val ∩ S) := by
    intro e he f hf hne
    exact (hM he hf hne).mono Finset.inter_subset_left Finset.inter_subset_left
  rw [covered, Finset.biUnion_inter, Finset.card_biUnion hd]
  rw [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ e ∈ M, ((e.val ∩ S).card + if Disjoint e.val S then 1 else 0) = ∑ _e ∈ M, 1 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : Disjoint e.val S
      · simp [h, Finset.disjoint_iff_inter_eq_empty.mp h]
      · simp only [h, ↓reduceIte, add_zero]
        have hpos : 0 < (e.val ∩ S).card := by
          apply Finset.card_pos.mpr
          exact Finset.nonempty_iff_ne_empty.mpr (fun hh => h (Finset.disjoint_iff_inter_eq_empty.mpr hh))
        have := hone e he
        omega
    _ = M.card := by simp

/-- An unconditional restricted cut-transfer case: if A itself is a matching
and has maximum ambient cardinality, no augmentation or recombination is
needed. K can still be a nonbipartite graph. -/
theorem cut_transfer_matching_host {A K J : Graph V} {IL IR : Finset V}
    (hA : Matching A) (hAK : A ⊆ K) (hAc : A.card = rank K)
    (hJ : Matching J) (hends : covered J ⊆ IL ∪ IR)
    (hcrossL : ∀ e ∈ A, (e.val ∩ IL).card ≤ 1)
    (hcrossR : ∀ e ∈ A, (e.val ∩ IR).card ≤ 1)
    (hc : ∀ e ∈ J, rank (insert e K) = rank K) :
    rank (A.filter fun e => Disjoint e.val IL) +
      rank (A.filter fun e => Disjoint e.val IR) + J.card ≤ 2 * rank K := by
  have hh := closed_matching_charge hJ hA hAK hA hAc (Finset.Subset.refl _)
    hends hc
  have hl := matching_deletion_identity hA hcrossL
  have hr := matching_deletion_identity hA hcrossR
  omega

end RandomOrderMatching.Graph
#print axioms RandomOrderMatching.Graph.closed_matching_charge
#print axioms RandomOrderMatching.Graph.cut_transfer_of_matching_witnesses
#print axioms RandomOrderMatching.Graph.cut_transfer_matching_host
