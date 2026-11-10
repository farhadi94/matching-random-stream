import RobustMatching.R2CutGraph

/-! Actual matching exchanges. These lemmas check a supplied finite exchange;
they do not assume, or claim to prove, Berge's augmenting-path existence theorem. -/
noncomputable section
set_option maxHeartbeats 800000
namespace RobustMatching.R2Cut
variable {V : Type*} [DecidableEq V]

theorem matching_union {M N : Graph V} (hM : Matching M) (hN : Matching N)
    (hd : Disjoint (covered M) (covered N)) : Matching (M ∪ N) := by
  intro e he f hf hne
  rcases Finset.mem_union.mp he with heM | heN <;>
    rcases Finset.mem_union.mp hf with hfM | hfN
  · exact hM heM hfM hne
  · exact hd.mono (fun v hv => mem_covered.mpr ⟨e, heM, hv⟩)
      (fun v hv => mem_covered.mpr ⟨f, hfN, hv⟩)
  · exact hd.symm.mono (fun v hv => mem_covered.mpr ⟨e, heN, hv⟩)
      (fun v hv => mem_covered.mpr ⟨f, hfM, hv⟩)
  · exact hN heN hfN hne

theorem edges_disjoint_of_covered_disjoint {M N : Graph V}
    (hd : Disjoint (covered M) (covered N)) : Disjoint M N := by
  apply Finset.disjoint_left.mpr
  intro e heM heN
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < e.val.card by rw [e.property]; decide)
  exact Finset.disjoint_left.mp hd (mem_covered.mpr ⟨e, heM, hv⟩)
    (mem_covered.mpr ⟨e, heN, hv⟩)

theorem covered_sdiff_disjoint {M D : Graph V} (hM : Matching M) (hDM : D ⊆ M) :
    Disjoint (covered (M \ D)) (covered D) := by
  apply Finset.disjoint_left.mpr
  intro v hvM hvD
  obtain ⟨e, he, hve⟩ := mem_covered.mp hvM
  obtain ⟨f, hf, hvf⟩ := mem_covered.mp hvD
  obtain ⟨heM, heD⟩ := Finset.mem_sdiff.mp he
  have hne : e ≠ f := fun h => heD (h ▸ hf)
  exact Finset.disjoint_left.mp (hM heM (hDM hf) hne) hve hvf

/-- Replace an explicit submatching by a disjoint-boundary matching. -/
theorem matching_patch {M D S : Graph V} (hM : Matching M) (hS : Matching S)
    (hd : Disjoint (covered (M \ D)) (covered S)) :
    Matching ((M \ D) ∪ S) :=
  matching_union (matching_mono hM Finset.sdiff_subset) hS hd

theorem patch_card {M D S : Graph V} (hDM : D ⊆ M)
    (hd : Disjoint (covered (M \ D)) (covered S)) :
    ((M \ D) ∪ S).card + D.card = M.card + S.card := by
  rw [Finset.card_union_of_disjoint (edges_disjoint_of_covered_disjoint hd),
    Finset.card_sdiff_of_subset hDM]
  have := Finset.card_le_card hDM
  omega

/-- A replacement that retains the removed vertices preserves all covered
vertices, even though it need not retain any removed matching edge. -/
theorem patch_covered_mono {M D S : Graph V}
    (hDS : covered D ⊆ covered S) : covered M ⊆ covered ((M \ D) ∪ S) := by
  intro v hv
  obtain ⟨e, he, hve⟩ := mem_covered.mp hv
  rw [covered_union]
  by_cases heD : e ∈ D
  · exact Finset.mem_union_right _ (hDS (mem_covered.mpr ⟨e, heD, hve⟩))
  · exact Finset.mem_union_left _ (mem_covered.mpr ⟨e, Finset.mem_sdiff.mpr ⟨he, heD⟩, hve⟩)

/-- A certified augmenting exchange is an actual larger matching with nested
covered vertex sets; cardinality and coverage are proved, not postulated. -/
theorem augmenting_exchange {M D S : Graph V}
    (hM : Matching M) (hDM : D ⊆ M) (hS : Matching S)
    (hd : Disjoint (covered (M \ D)) (covered S))
    (hcov : covered D ⊆ covered S) (hc : S.card = D.card + 1) :
    Matching ((M \ D) ∪ S) ∧
    covered M ⊆ covered ((M \ D) ∪ S) ∧
    ((M \ D) ∪ S).card = M.card + 1 := by
  have hh := patch_card hDM hd
  exact ⟨matching_patch hM hS hd, patch_covered_mono hcov, by omega⟩

/-- Restrict a matching to edges contained in a prescribed vertex block. -/
def inside (M : Graph V) (S : Finset V) : Graph V := M.filter fun e => e.val ⊆ S

/-- A block has no boundary edges in M. This is directly decidable on the
supplied matching, and is satisfied by every union of M∪N components. -/
def ClosedBlock (M : Graph V) (S : Finset V) : Prop :=
  ∀ e ∈ M, e.val ⊆ S ∨ Disjoint e.val S

theorem inside_covered_subset (M : Graph V) (S : Finset V) :
    covered (inside M S) ⊆ S := by
  intro v hv
  obtain ⟨e, he, hve⟩ := mem_covered.mp hv
  exact (Finset.mem_filter.mp he).2 hve

theorem outside_covered_disjoint {M : Graph V} {S : Finset V}
    (hc : ClosedBlock M S) : Disjoint (covered (M \ inside M S)) S := by
  apply Finset.disjoint_left.mpr
  intro v hv hvS
  obtain ⟨e, he, hve⟩ := mem_covered.mp hv
  obtain ⟨heM, heI⟩ := Finset.mem_sdiff.mp he
  rcases hc e heM with hi | hd
  · exact heI (Finset.mem_filter.mpr ⟨heM, hi⟩)
  · exact Finset.disjoint_left.mp hd hve hvS

theorem block_splice_matching {M N : Graph V} {S : Finset V}
    (hM : Matching M) (hN : Matching N) (hc : ClosedBlock M S) :
    Matching ((M \ inside M S) ∪ inside N S) := by
  exact matching_patch hM (matching_mono hN (Finset.filter_subset _ _))
    ((outside_covered_disjoint hc).mono_right (inside_covered_subset N S))

theorem block_splice_subset {K M N : Graph V} (hMK : M ⊆ K) (hNK : N ⊆ K)
    (S : Finset V) : (M \ inside M S) ∪ inside N S ⊆ K := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hMK (Finset.mem_sdiff.mp he).1
  · exact hNK (Finset.mem_filter.mp he).1

/-- Recombining any closed block of two maximum matchings remains maximum.
Equal component edge counts are derived from maximal cardinality on both
sides, rather than supplied as a premise. -/
theorem maximum_block_splice {K M N : Graph V} {S : Finset V}
    (hMK : M ⊆ K) (hNK : N ⊆ K) (hM : Matching M) (hN : Matching N)
    (hMc : M.card = rank K) (hNc : N.card = rank K)
    (hcM : ClosedBlock M S) (hcN : ClosedBlock N S) :
    (inside M S).card = (inside N S).card ∧
    Matching ((M \ inside M S) ∪ inside N S) ∧
    ((M \ inside M S) ∪ inside N S).card = rank K := by
  have hm := block_splice_matching hM hN hcM
  have hn := block_splice_matching hN hM hcN
  have hmb := matching_card_le_rank (block_splice_subset hMK hNK S) hm
  have hnb := matching_card_le_rank (block_splice_subset hNK hMK S) hn
  have hma := patch_card (M := M) (D := inside M S) (S := inside N S)
    (show inside M S ⊆ M from Finset.filter_subset _ _)
    ((outside_covered_disjoint hcM).mono_right (inside_covered_subset N S))
  have hna := patch_card (M := N) (D := inside N S) (S := inside M S)
    (show inside N S ⊆ N from Finset.filter_subset _ _)
    ((outside_covered_disjoint hcN).mono_right (inside_covered_subset M S))
  constructor
  · omega
  · exact ⟨hm, by omega⟩

theorem covered_inside {M : Graph V} {S : Finset V} (hc : ClosedBlock M S) :
    covered (inside M S) = covered M ∩ S := by
  ext v
  constructor
  · intro hv
    exact Finset.mem_inter.mpr ⟨covered_mono (Finset.filter_subset _ _) hv,
      inside_covered_subset M S hv⟩
  · intro hv
    obtain ⟨hvM, hvS⟩ := Finset.mem_inter.mp hv
    obtain ⟨e, he, hve⟩ := mem_covered.mp hvM
    rcases hc e he with hi | hd
    · exact mem_covered.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hi⟩, hve⟩
    · exact (Finset.disjoint_left.mp hd hve hvS).elim

theorem covered_outside {M : Graph V} {S : Finset V} (hc : ClosedBlock M S) :
    covered (M \ inside M S) = covered M \ S := by
  ext v
  constructor
  · intro hv
    exact Finset.mem_sdiff.mpr ⟨covered_mono Finset.sdiff_subset hv,
      fun hvS => Finset.disjoint_left.mp (outside_covered_disjoint hc) hv hvS⟩
  · intro hv
    obtain ⟨hvM, hvS⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨e, he, hve⟩ := mem_covered.mp hvM
    refine mem_covered.mpr ⟨e, Finset.mem_sdiff.mpr ⟨he, ?_⟩, hve⟩
    intro hi
    exact hvS ((Finset.mem_filter.mp hi).2 hve)

/-- Exact covered-vertex formula for the recombination used in cut transfer. -/
theorem covered_block_splice {M N : Graph V} {S : Finset V}
    (hcM : ClosedBlock M S) (hcN : ClosedBlock N S) :
    covered ((M \ inside M S) ∪ inside N S) = (covered M \ S) ∪ (covered N ∩ S) := by
  rw [covered_union, covered_outside hcM, covered_inside hcN]

/-- Given a closed union of alternating components, it suffices to check
that outside the block the left coverage agrees, and inside it the right
coverage agrees. The resulting splice then inherits N's entire left
coverage and M's entire right coverage simultaneously. -/
theorem block_splice_side_coverage {M N : Graph V} {S L R : Finset V}
    (hcM : ClosedBlock M S) (hcN : ClosedBlock N S)
    (hL : ∀ v ∈ L, v ∉ S → (v ∈ covered M ↔ v ∈ covered N))
    (hR : ∀ v ∈ R, v ∈ S → (v ∈ covered M ↔ v ∈ covered N)) :
    covered ((M \ inside M S) ∪ inside N S) ∩ L = covered N ∩ L ∧
    covered ((M \ inside M S) ∪ inside N S) ∩ R = covered M ∩ R := by
  rw [covered_block_splice hcM hcN]
  constructor
  · ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    by_cases hvL : v ∈ L <;> by_cases hvS : v ∈ S
    · simp [hvL, hvS]
    · simp [hvL, hvS, hL v hvL hvS]
    · simp [hvL]
    · simp [hvL]
  · ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    by_cases hvR : v ∈ R <;> by_cases hvS : v ∈ S
    · simp [hvR, hvS, hR v hvR hvS]
    · simp [hvR, hvS]
    · simp [hvR]
    · simp [hvR]

end RobustMatching.R2Cut
#print axioms RobustMatching.R2Cut.augmenting_exchange
#print axioms RobustMatching.R2Cut.maximum_block_splice
#print axioms RobustMatching.R2Cut.block_splice_side_coverage
