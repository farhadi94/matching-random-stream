import RandomOrderMatching.Graph.EvenFactor.Coloring

/-! Even directed factors yield actual marked matching pairs, using
finite incidence counts and componentwise color reversal. -/

noncomputable section
open scoped BigOperators symmDiff
open Classical

namespace RandomOrderMatching.Graph.EvenFactor
open RandomOrderMatching.Graph RandomOrderMatching.Graph.Konig
open RandomOrderMatching.Graph.Components RandomOrderMatching.Graph.BipartiteExchange
open RandomOrderMatching.Graph.MarkedPair RandomOrderMatching.Graph.MarkedPair.CutWitnesses

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem arcGraph_card_le (F : Finset (V × V)) : (arcGraph F).card ≤ F.card := by
  have h₁ : (arcGraph F).card ≤ (looplessArcs F).card := Finset.card_image_le
  have h₂ : (looplessArcs F).card ≤ (F.filter fun p => p.1 ≠ p.2).card := by
    exact (Finset.card_image_le).trans (by rw [Finset.card_attach])
  exact h₁.trans (h₂.trans (Finset.card_filter_le _ _))

theorem inside_arcGraph_subset (F : Finset (V × V)) (S : Finset V) :
    inside (arcGraph F) S ⊆ arcGraph (F.filter fun p => p.2 ∈ S) := by
  intro e he
  obtain ⟨heF,heS⟩ := Finset.mem_filter.mp he
  obtain ⟨p,hp,hne,rfl⟩ := mem_arcGraph.mp heF
  have hs : p.2 ∈ S := heS (by simp [arcEdge])
  exact mem_arcGraph.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hs⟩,hne,rfl⟩

/-- An actual partial permutation component has at most one vertex absent
from its target support. Thus forbidden columns are separated. -/
theorem target_avoiding_marks_separated (F : Finset (V × V)) (marks : Finset V)
    (hinj : Set.InjOn Prod.snd (F : Set (V × V)))
    (ha : Disjoint (targetSupport F) marks) : Separated (arcGraph F) marks := by
  intro u hu v hv hr
  let c := (simpleGraph (arcGraph F)).connectedComponentMk u
  let S := componentVertices (arcGraph F) c
  let D := F.filter fun p => p.2 ∈ S
  let T := targetSupport D
  have hTS : T ⊆ S := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hp).2
  have hTc : T.card = D.card := by
    exact Finset.card_image_of_injOn (fun a ha b hb he =>
      hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 he)
  have hconn := component_card_le_edges_add_one (arcGraph F) c
  have hinside := Finset.card_le_card (inside_arcGraph_subset F S)
  have hcard := arcGraph_card_le D
  have hdiff := Finset.card_sdiff_of_subset hTS
  have hle : (S \ T).card ≤ 1 := by
    change S.card ≤ (inside (arcGraph F) S).card + 1 at hconn
    change (inside (arcGraph F) S).card ≤ (arcGraph D).card at hinside
    omega
  have hmarks : ∀ x ∈ marks, x ∈ S → x ∈ S \ T := by
    intro x hx hxS
    refine Finset.mem_sdiff.mpr ⟨hxS,?_⟩
    intro hxT
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hxT
    exact Finset.disjoint_left.mp ha
      (Finset.mem_image_of_mem Prod.snd (Finset.mem_filter.mp hp).1) hx
  have huS : u ∈ S := by simp [S,c,componentVertices]
  have hvS : v ∈ S := by
    simpa [S,c,componentVertices] using (SimpleGraph.ConnectedComponent.sound hr).symm
  exact Finset.card_le_one.mp hle u (hmarks u hu huS) v (hmarks v hv hvS)

/-- Orient a bipartition so every separated marked vertex lies on the
second side. Only actual connected components are used. -/
theorem orient_cut_away_from_marks (G : Graph V) (C marks : Finset V)
    (hc : Crosses G C) (hs : Separated G marks) :
    ∃ D : Finset V, Crosses G D ∧ Disjoint D marks := by
  let p : (simpleGraph G).ConnectedComponent → Prop := fun c =>
    ∃ u ∈ marks, u ∈ C ∧ (simpleGraph G).connectedComponentMk u = c
  let S := selectedComponents G p
  have hclosed := selected_components_closed G p
  refine ⟨C ∆ S,crosses_flip_closed hc hclosed,Finset.disjoint_left.mpr ?_⟩
  intro v hv hm
  have hiff : v ∈ C ↔ v ∈ S := by
    constructor
    · intro hvC
      simp only [S,selectedComponents,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨v,hm,hvC,rfl⟩
    · intro hvS
      have hp : p ((simpleGraph G).connectedComponentMk v) := by
        simpa only [S,selectedComponents,Finset.mem_filter,Finset.mem_univ,true_and] using hvS
      obtain ⟨u,hu,huC,heq⟩ := hp
      have huv := hs u hu v hm (SimpleGraph.ConnectedComponent.exact heq)
      exact huv ▸ huC
  simp only [Finset.mem_symmDiff] at hv
  rcases hv with ⟨hvC,hvS⟩ | ⟨hvS,hvC⟩
  · exact hvS (hiff.mp hvC)
  · exact hvC (hiff.mpr hvS)

theorem crossing_edge_sides {G : Graph V} {C : Finset V} (hc : Crosses G C)
    {e : Edge V} (he : e ∈ G) {u v : V} (hu : u ∈ e.val) (hv : v ∈ e.val)
    (hn : u ≠ v) : u ∈ C ↔ v ∉ C := by
  constructor
  · intro huC hvC
    exact hn (Finset.card_le_one.mp (hc e he).le u (Finset.mem_inter.mpr ⟨hu,huC⟩)
      v (Finset.mem_inter.mpr ⟨hv,hvC⟩))
  · intro hvC
    by_contra huC
    exact hn (Finset.card_le_one.mp (crosses_compl hc e he).le u
      (Finset.mem_inter.mpr ⟨hu,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,huC⟩⟩)
      v (Finset.mem_inter.mpr ⟨hv,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hvC⟩⟩))

theorem same_side_arcs_matching (F : Finset (V × V)) (C : Finset V)
    (hm : RandomOrderMatching.Graph.BipartiteDual.IsMatching F)
    (hs : ∀ p ∈ F, p.1 ∈ C ∧ p.2 ∉ C) : Matching (arcGraph F) := by
  intro e he f hf hne
  obtain ⟨p,hp,hpn,rfl⟩ := mem_arcGraph.mp he
  obtain ⟨q,hq,hqn,rfl⟩ := mem_arcGraph.mp hf
  apply Finset.disjoint_left.mpr
  intro v hvp hvq
  simp only [arcEdge,Finset.mem_insert,Finset.mem_singleton] at hvp hvq
  have hpC := hs p hp
  have hqC := hs q hq
  rcases hvp with hvp | hvp <;> rcases hvq with hvq | hvq
  · have hpq := hm.1 hp hq (hvp.symm.trans hvq)
    exact hne (by subst q; rfl)
  · exact hqC.2 ((hvp.symm.trans hvq) ▸ hpC.1)
  · exact hpC.2 ((hvq.symm.trans hvp) ▸ hqC.1)
  · have hpq := hm.2 hp hq (hvp.symm.trans hvq)
    exact hne (by subst q; rfl)

theorem same_side_arcEdge_inj (F : Finset (V × V)) (C : Finset V)
    (hm : RandomOrderMatching.Graph.BipartiteDual.IsMatching F)
    (hs : ∀ p ∈ F, p.1 ∈ C ∧ p.2 ∉ C)
    {p q : V × V} (hp : p ∈ F) (hq : q ∈ F) (hpn : p.1 ≠ p.2) (hqn : q.1 ≠ q.2)
    (heq : arcEdge p hpn = arcEdge q hqn) : p = q := by
  have hval := congrArg Subtype.val heq
  have hmem : p.1 ∈ (arcEdge q hqn).val := by rw [← hval]; simp [arcEdge]
  simp only [arcEdge,Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with he | he
  · exact hm.1 hp hq he
  · exact ((hs q hq).2 (he ▸ (hs p hp).1)).elim

theorem same_side_arcs_weight (F : Finset (V × V)) (C : Finset V)
    (hm : RandomOrderMatching.Graph.BipartiteDual.IsMatching F)
    (hs : ∀ p ∈ F, p.1 ∈ C ∧ p.2 ∉ C) (w : Edge V → ℝ) :
    (∑ e ∈ arcGraph F, w e) = ∑ p ∈ F, arcWeight w p := by
  have hn (p : V × V) (hp : p ∈ F) : p.1 ≠ p.2 :=
    fun he => (hs p hp).2 (he ▸ (hs p hp).1)
  symm
  apply Finset.sum_bij (fun p hp => arcEdge p (hn p hp))
  · intro p hp
    exact mem_arcGraph.mpr ⟨p,hp,hn p hp,rfl⟩
  · intro p hp q hq he
    exact same_side_arcEdge_inj F C hm hs hp hq _ _ he
  · intro e he
    obtain ⟨p,hp,hpn,hpe⟩ := mem_arcGraph.mp he
    exact ⟨p,hp,hpe⟩
  · intro p hp
    exact arcWeight_eq w p (hn p hp)

theorem arcGraph_mono {F H : Finset (V × V)} (h : F ⊆ H) : arcGraph F ⊆ arcGraph H := by
  intro e he
  obtain ⟨p,hp,hpn,hpe⟩ := mem_arcGraph.mp he
  exact mem_arcGraph.mpr ⟨p,h hp,hpn,hpe⟩

/-- Every actual even factor has a marked matching-pair realization that
preserves every edge-weight sum, including doubled opposite arcs. -/
theorem evenFactor_to_admissible (F : Finset (V × V)) (hf : EvenFactor F)
    (marks : Finset V) (ha : Disjoint (targetSupport F) marks) :
    ∃ N₁ N₂ : Graph V, N₁ ⊆ arcGraph F ∧ N₂ ⊆ arcGraph F ∧
      Admissible N₁ N₂ marks ∧
      ∀ w : Edge V → ℝ, pairWeight w (N₁,N₂) = ∑ p ∈ F, arcWeight w p := by
  have hsep := target_avoiding_marks_separated F marks hf.matching.2 ha
  have hcol : (simpleGraph (arcGraph F)).Colorable 2 := by
    rw [arcGraph_simpleGraph]
    exact hf.colorable
  obtain ⟨C,hC⟩ := exists_crosses_of_colorable (arcGraph F) hcol
  obtain ⟨D,hD,hdm⟩ := orient_cut_away_from_marks (arcGraph F) C marks hC hsep
  let F₁ := F.filter fun p => p.1 ∈ D
  let F₂ := F.filter fun p => p.1 ∉ D
  have hm₁ : RandomOrderMatching.Graph.BipartiteDual.IsMatching F₁ :=
    ⟨hf.matching.1.mono (Finset.filter_subset _ _),hf.matching.2.mono (Finset.filter_subset _ _)⟩
  have hm₂ : RandomOrderMatching.Graph.BipartiteDual.IsMatching F₂ :=
    ⟨hf.matching.1.mono (Finset.filter_subset _ _),hf.matching.2.mono (Finset.filter_subset _ _)⟩
  have hsides (p : V × V) (hp : p ∈ F) : p.1 ∈ D ↔ p.2 ∉ D :=
    crossing_edge_sides hD (mem_arcGraph.mpr ⟨p,hp,hf.loopless p hp,rfl⟩)
      (by simp [arcEdge]) (by simp [arcEdge]) (hf.loopless p hp)
  have hs₁ : ∀ p ∈ F₁, p.1 ∈ D ∧ p.2 ∉ D := by
    intro p hp
    obtain ⟨hpF,hpD⟩ := Finset.mem_filter.mp hp
    exact ⟨hpD,(hsides p hpF).mp hpD⟩
  have hs₂ : ∀ p ∈ F₂, p.1 ∈ Finset.univ \ D ∧ p.2 ∉ Finset.univ \ D := by
    intro p hp
    obtain ⟨hpF,hpD⟩ := Finset.mem_filter.mp hp
    have ht : p.2 ∈ D := by by_contra hn; exact hpD ((hsides p hpF).mpr hn)
    exact ⟨by simp [hpD],by simp [ht]⟩
  let N₁ := arcGraph F₁
  let N₂ := arcGraph F₂
  have hn₁ : Matching N₁ := same_side_arcs_matching F₁ D hm₁ hs₁
  have hn₂ : Matching N₂ := same_side_arcs_matching F₂ (Finset.univ \ D) hm₂ hs₂
  have hsub₁ : N₁ ⊆ arcGraph F := arcGraph_mono (Finset.filter_subset _ _)
  have hsub₂ : N₂ ⊆ arcGraph F := arcGraph_mono (Finset.filter_subset _ _)
  have hav : Disjoint (covered N₁) marks := by
    apply Finset.disjoint_left.mpr
    intro v hv hm
    obtain ⟨e,he,hve⟩ := mem_covered.mp hv
    obtain ⟨p,hp,hpn,rfl⟩ := mem_arcGraph.mp he
    simp only [arcEdge,Finset.mem_insert,Finset.mem_singleton] at hve
    rcases hve with rfl | rfl
    · exact Finset.disjoint_left.mp hdm (hs₁ p hp).1 hm
    · exact Finset.disjoint_left.mp ha
        (Finset.mem_image_of_mem Prod.snd (Finset.mem_filter.mp hp).1) hm
  have hsd : N₁ ∆ N₂ ⊆ arcGraph F := by
    intro e he
    rcases Finset.mem_union.mp (Finset.symmDiff_subset_union he) with he | he
    · exact hsub₁ he
    · exact hsub₂ he
  refine ⟨N₁,N₂,hsub₁,hsub₂,⟨hn₁,hn₂,hav,separated_mono hsd hsep⟩,?_⟩
  intro w
  unfold pairWeight
  rw [same_side_arcs_weight F₁ D hm₁ hs₁ w,
    same_side_arcs_weight F₂ (Finset.univ \ D) hm₂ hs₂ w]
  exact Finset.sum_filter_add_sum_filter_not F (fun p => p.1 ∈ D) (arcWeight w)

end RandomOrderMatching.Graph.EvenFactor

set_option pp.fullNames true
#print axioms RandomOrderMatching.Graph.EvenFactor.evenFactor_to_admissible
