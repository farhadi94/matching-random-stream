import RandomOrderMatching.HistoricalDeletion.Matching
import RandomOrderMatching.Graph.MarkedPair.CutWitnesses
import RandomOrderMatching.Graph.BipartiteDual.Lattice

/-! Native bipartite endpoint pairs inside an arbitrary actual vertex type.
The ambient historical host remains a general graph on V throughout. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace RandomOrderMatching.HistoricalDeletion.CutEncoding
open RandomOrderMatching.Graph RandomOrderMatching.Graph.MarkedPair
open RandomOrderMatching.Graph.WeightedMatching RandomOrderMatching.Graph.BipartiteExchange
open RandomOrderMatching.HistoricalDeletion.Matching
variable {V : Type*} [Fintype V] [LinearOrder V]

abbrev Left (C : Finset V) := {v : V // v ∈ C}
abbrev Right (C : Finset V) := {v : V // v ∉ C}

def edgeOf (C : Finset V) (p : Left C × Right C) : Edge V :=
  ⟨{p.1.val,p.2.val},by
    have h : p.1.val ≠ p.2.val := fun he => p.2.property (he ▸ p.1.property)
    simp [h]⟩

theorem edgeOf_injective (C : Finset V) : Function.Injective (edgeOf C) := by
  intro p q hh
  have hv := congrArg Subtype.val hh
  have hl : p.1.val ∈ (edgeOf C q).val := by rw [←hv]; simp [edgeOf]
  have hr : p.2.val ∈ (edgeOf C q).val := by rw [←hv]; simp [edgeOf]
  simp only [edgeOf,Finset.mem_insert,Finset.mem_singleton] at hl hr
  apply Prod.ext
  · apply Subtype.ext
    exact hl.resolve_right (fun h => q.2.property (h ▸ p.1.property))
  · apply Subtype.ext
    exact hr.resolve_left (fun h => p.2.property (h ▸ q.1.property))

def encode (C : Finset V) (E : Finset (Left C × Right C)) : Graph V :=
  E.image (edgeOf C)

def leftMarks (C : Finset V) (E : Finset (Left C × Right C)) : Finset V :=
  E.image (fun p => p.1.val)

def rightMarks (C : Finset V) (E : Finset (Left C × Right C)) : Finset V :=
  E.image (fun p => p.2.val)

theorem encode_matching (C : Finset V) (E : Finset (Left C × Right C))
    (hm : RandomOrderMatching.Graph.BipartiteDual.IsMatching E) : Matching (encode C E) := by
  intro e he f hf hne
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hf
  apply Finset.disjoint_left.mpr
  intro v hvp hvq
  simp only [edgeOf,Finset.mem_insert,Finset.mem_singleton] at hvp hvq
  rcases hvp with rfl | rfl <;> rcases hvq with hh | hh
  · exact hne (congrArg (edgeOf C) (hm.1 hp hq (Subtype.ext hh)))
  · exact q.2.property (hh ▸ p.1.property)
  · exact p.2.property (hh.symm ▸ q.1.property)
  · exact hne (congrArg (edgeOf C) (hm.2 hp hq (Subtype.ext hh)))

theorem encode_mono (C : Finset V) {E F : Finset (Left C × Right C)} (h : E ⊆ F) :
    encode C E ⊆ encode C F := Finset.image_subset_image h

theorem encode_sum (C : Finset V) (E : Finset (Left C × Right C)) (w : Edge V → ℝ) :
    (∑ e ∈ encode C E, w e) = ∑ p ∈ E, w (edgeOf C p) :=
  Finset.sum_image (edgeOf_injective C).injOn

theorem encode_covered (C : Finset V) (E : Finset (Left C × Right C)) :
    covered (encode C E) = leftMarks C E ∪ rightMarks C E := by
  ext v
  constructor
  · intro hv
    obtain ⟨e,he,hve⟩ := mem_covered.mp hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    simp only [edgeOf,Finset.mem_insert,Finset.mem_singleton] at hve
    rcases hve with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,h.symm⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with hl | hr
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
      exact mem_covered.mpr ⟨edgeOf C p,Finset.mem_image_of_mem _ hp,by simp [edgeOf]⟩
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
      exact mem_covered.mpr ⟨edgeOf C p,Finset.mem_image_of_mem _ hp,by simp [edgeOf]⟩

theorem encode_crosses (C : Finset V) (E : Finset (Left C × Right C)) :
    Crosses (encode C E) C := by
  intro e he
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
  have hi : (edgeOf C p).val ∩ C = {p.1.val} := by
    ext v
    simp only [edgeOf,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨h,hv⟩
      exact h.resolve_right (fun hh => p.2.property (hh ▸ hv))
    · intro h
      exact ⟨Or.inl h,h ▸ p.1.property⟩
  rw [hi]
  simp

theorem leftMarks_subset (C : Finset V) (E : Finset (Left C × Right C)) :
    leftMarks C E ⊆ C := by
  intro v hv
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
  exact p.1.property

theorem rightMarks_subset (C : Finset V) (E : Finset (Left C × Right C)) :
    rightMarks C E ⊆ Finset.univ \ C := by
  intro v hv
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,p.2.property⟩

theorem encode_avoids_left (C : Finset V) (M T : Finset (Left C × Right C))
    (hd : Disjoint (M.image Prod.fst) (T.image Prod.fst)) :
    Disjoint (covered (encode C M)) (leftMarks C T) := by
  apply Finset.disjoint_left.mpr
  intro v hv ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  rw [encode_covered] at hv
  rcases Finset.mem_union.mp hv with hl | hr
  · obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hl
    have heq : q.1 = p.1 := Subtype.ext hqp
    exact Finset.disjoint_left.mp hd (Finset.mem_image.mpr ⟨q,hq,heq⟩)
      (Finset.mem_image_of_mem _ hp)
  · obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hr
    exact q.2.property (hqp.symm ▸ p.1.property)

theorem encode_avoids_right (C : Finset V) (M T : Finset (Left C × Right C))
    (hd : Disjoint (M.image Prod.snd) (T.image Prod.snd)) :
    Disjoint (covered (encode C M)) (rightMarks C T) := by
  apply Finset.disjoint_left.mpr
  intro v hv ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  rw [encode_covered] at hv
  rcases Finset.mem_union.mp hv with hl | hr
  · obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hl
    exact p.2.property (hqp ▸ q.1.property)
  · obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hr
    have heq : q.2 = p.2 := Subtype.ext hqp
    exact Finset.disjoint_left.mp hd (Finset.mem_image.mpr ⟨q,hq,heq⟩)
      (Finset.mem_image_of_mem _ hp)

/-- The complete actual historical graph hypothesis yields the hereditary
matching-triple input required by integral auxiliary duality. P is arbitrary. -/
theorem historical_triple_bound
    (C : Finset V) (w : Edge V → ℕ) (K : ℕ → Graph V)
    (hK : ∀ i j, i ≤ j → K i ⊆ K j) (n : ℕ)
    (E P : Finset (Left C × Right C)) (hE : encode C E ⊆ K 0)
    (hclosed : ∀ e ∈ encode C P, ∃ t ≤ n,
      opt (fun f => (w f : ℝ)) (insert e (K t)) = opt (fun f => (w f : ℝ)) (K t))
    (M1 M2 T : Finset (Left C × Right C))
    (h1 : RandomOrderMatching.Graph.BipartiteDual.IsMatching M1) (h2 : RandomOrderMatching.Graph.BipartiteDual.IsMatching M2)
    (hT : RandomOrderMatching.Graph.BipartiteDual.IsMatching T) (hs1 : M1 ⊆ E) (hs2 : M2 ⊆ E) (hsT : T ⊆ P)
    (hd1 : Disjoint (M1.image Prod.fst) (T.image Prod.fst))
    (hd2 : Disjoint (M2.image Prod.snd) (T.image Prod.snd)) :
    (∑ e ∈ M1, w (edgeOf C e)) + (∑ e ∈ M2, w (edgeOf C e)) +
      (∑ e ∈ T, w (edgeOf C e)) ≤ 2 * RandomOrderMatching.Phases.WeightedState.natOpt w (K n) := by
  let wr : Edge V → ℝ := fun e => (w e : ℝ)
  obtain ⟨N1,hN1,N2,hN2,hadm,hwt⟩ := RandomOrderMatching.Graph.MarkedPair.CutWitnesses.cut_pair_admissible wr
    (encode_mono C hs1) (encode_mono C hs2) (encode_matching C M1 h1)
    (encode_matching C M2 h2) (encode_crosses C E) (leftMarks_subset C T)
    (rightMarks_subset C T) (encode_avoids_left C M1 T hd1) (encode_avoids_right C M2 T hd2)
  have hp := pairWeight_le_pathValue wr (hN1.trans hE) (hN2.trans hE) hadm
  rw [hwt,←encode_covered] at hp
  have hh := historical_every_matching wr (fun _ => Nat.cast_nonneg _) K hK n
    (encode C P) hclosed (encode C T) (encode_mono C hsT) (encode_matching C T hT)
  unfold pairWeight at hp
  rw [encode_sum,encode_sum] at hp
  rw [encode_sum,RandomOrderMatching.Phases.WeightedState.opt_eq_natOpt] at hh
  have hreal : (∑ e ∈ M1, (w (edgeOf C e) : ℝ)) +
      (∑ e ∈ M2, (w (edgeOf C e) : ℝ)) + (∑ e ∈ T, (w (edgeOf C e) : ℝ)) ≤
        2 * (RandomOrderMatching.Phases.WeightedState.natOpt w (K n) : ℝ) := by dsimp [wr] at hp hh; linarith
  exact_mod_cast hreal

end RandomOrderMatching.HistoricalDeletion.CutEncoding

#print axioms RandomOrderMatching.HistoricalDeletion.CutEncoding.historical_triple_bound
