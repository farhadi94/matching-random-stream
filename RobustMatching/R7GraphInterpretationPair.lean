import RobustMatching.R7GraphInterpretationFactor

/-! Actual marked matching pairs yield loop-free partial permutations,
preserving edge multiplicities and forbidden columns. -/

noncomputable section
open scoped BigOperators symmDiff
open Classical

namespace RobustMatching.R7GraphInterpretation
open RobustMatching.R2Cut RobustMatching.R7GraphKonig
open RobustMatching.R7GraphComponents RobustMatching.R7GraphBipartiteExchange
open RobustMatching.R7AlgebraPath RobustMatching.R7GraphMarked

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exclusive_edge_disjoint_common {P Q : Graph V} (hP : Matching P) (hQ : Matching Q)
    {e : Edge V} (he : e ∈ P ∪ Q) (hne : e ∉ P ∩ Q) :
    Disjoint e.val (covered (P ∩ Q)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hvcommon
  obtain ⟨f,hf,hvf⟩ := mem_covered.mp hvcommon
  have hnef : e ≠ f := fun hh => hne (hh ▸ hf)
  rcases Finset.mem_union.mp he with he | he
  · exact Finset.disjoint_left.mp (hP he (Finset.mem_inter.mp hf).1 hnef) hv hvf
  · exact Finset.disjoint_left.mp (hQ he (Finset.mem_inter.mp hf).2 hnef) hv hvf

theorem union_adj_outside_common {P Q : Graph V} (hP : Matching P) (hQ : Matching Q)
    {u v : V} (h : (simpleGraph (P ∪ Q)).Adj u v) (hu : u ∉ covered (P ∩ Q)) :
    (simpleGraph (P ∆ Q)).Adj u v ∧ v ∉ covered (P ∩ Q) := by
  obtain ⟨⟨e,he,heq⟩,hn⟩ := h
  have hue : u ∈ e.val := by rw [← heq]; simp
  have hve : v ∈ e.val := by rw [← heq]; simp
  have hne : e ∉ P ∩ Q := fun hh => hu (mem_covered.mpr ⟨e,hh,hue⟩)
  have heX : e ∈ P ∆ Q := by
    simp only [Finset.mem_symmDiff]
    rcases Finset.mem_union.mp he with hp | hq
    · exact Or.inl ⟨hp,fun hq => hne (Finset.mem_inter.mpr ⟨hp,hq⟩)⟩
    · exact Or.inr ⟨hq,fun hp => hne (Finset.mem_inter.mpr ⟨hp,hq⟩)⟩
  exact ⟨⟨⟨e,heX,heq⟩,hn⟩,fun hv =>
    Finset.disjoint_left.mp (exclusive_edge_disjoint_common hP hQ he hne) hve hv⟩

theorem union_reachable_outside_common {P Q : Graph V} (hP : Matching P) (hQ : Matching Q)
    {u v : V} (h : (simpleGraph (P ∪ Q)).Reachable u v) (hu : u ∉ covered (P ∩ Q)) :
    (simpleGraph (P ∆ Q)).Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons hadj p ih =>
      obtain ⟨ha,hnext⟩ := union_adj_outside_common hP hQ hadj hu
      exact ha.reachable.trans (ih hnext)

theorem admissible_union_separated {P Q : Graph V} {marks : Finset V}
    (ha : Admissible P Q marks) : Separated (P ∪ Q) marks := by
  intro u hu v hv hr
  have hnot : u ∉ covered (P ∩ Q) := fun hh => Finset.disjoint_left.mp ha.2.2.1
    (covered_mono Finset.inter_subset_left hh) hu
  exact ha.2.2.2 u hu v hv (union_reachable_outside_common ha.1 ha.2.1 hr hnot)

def orientedArcs (M : Graph V) (C : Finset V) : Finset (V × V) :=
  Finset.univ.filter fun p => p.1 ∈ C ∧ p.2 ∉ C ∧
    ∃ hp : p.1 ≠ p.2, arcEdge p hp ∈ M

theorem mem_orientedArcs {M : Graph V} {C : Finset V} {p : V × V} :
    p ∈ orientedArcs M C ↔ p.1 ∈ C ∧ p.2 ∉ C ∧
      ∃ hp : p.1 ≠ p.2, arcEdge p hp ∈ M := by simp [orientedArcs]

theorem oriented_arcEdge_injective (C : Finset V) {p q : V × V}
    (hp : p.1 ∈ C ∧ p.2 ∉ C) (hq : q.1 ∈ C ∧ q.2 ∉ C)
    (hpn : p.1 ≠ p.2) (hqn : q.1 ≠ q.2)
    (heq : arcEdge p hpn = arcEdge q hqn) : p = q := by
  have hval := congrArg Subtype.val heq
  have h₁ : p.1 ∈ (arcEdge q hqn).val := by rw [← hval]; simp [arcEdge]
  have h₂ : p.2 ∈ (arcEdge q hqn).val := by rw [← hval]; simp [arcEdge]
  simp only [arcEdge,Finset.mem_insert,Finset.mem_singleton] at h₁ h₂
  have he₁ : p.1 = q.1 := h₁.resolve_right (fun hh => hq.2 (hh ▸ hp.1))
  have he₂ : p.2 = q.2 := h₂.resolve_left (fun hh => hp.2 (hh.symm ▸ hq.1))
  exact Prod.ext he₁ he₂

theorem orientedArcs_matching (M : Graph V) (C : Finset V) (hM : Matching M) :
    RobustMatching.Dual.IsMatching (orientedArcs M C) := by
  have aux (p q : V × V) (hp : p ∈ orientedArcs M C) (hq : q ∈ orientedArcs M C)
      (hx : p.1 = q.1 ∨ p.2 = q.2) : p = q := by
    obtain ⟨hpC,hpN,hpn,hpM⟩ := mem_orientedArcs.mp hp
    obtain ⟨hqC,hqN,hqn,hqM⟩ := mem_orientedArcs.mp hq
    by_cases heq : arcEdge p hpn = arcEdge q hqn
    · exact oriented_arcEdge_injective C ⟨hpC,hpN⟩ ⟨hqC,hqN⟩ hpn hqn heq
    · have hd := hM hpM hqM heq
      rcases hx with hx | hx
      · exact (Finset.disjoint_left.mp hd (show p.1 ∈ (arcEdge p hpn).val by simp [arcEdge])
          (by simp [arcEdge,hx])).elim
      · exact (Finset.disjoint_left.mp hd (show p.2 ∈ (arcEdge p hpn).val by simp [arcEdge])
          (by simp [arcEdge,hx])).elim
  exact ⟨fun p hp q hq he => aux p q hp hq (Or.inl he),
    fun p hp q hq he => aux p q hp hq (Or.inr he)⟩

theorem arcGraph_orientedArcs (M : Graph V) (C : Finset V) (hc : Crosses M C) :
    arcGraph (orientedArcs M C) = M := by
  ext e
  constructor
  · intro he
    obtain ⟨p,hp,hpn,rfl⟩ := mem_arcGraph.mp he
    obtain ⟨_,_,hpne,hpM⟩ := mem_orientedArcs.mp hp
    exact hpM
  · intro he
    obtain ⟨u,v,hn,hev⟩ := Finset.card_eq_two.mp e.property
    have hu : u ∈ e.val := by rw [hev]; simp
    have hv : v ∈ e.val := by rw [hev]; simp
    have hsides := crossing_edge_sides hc he hu hv hn
    by_cases huC : u ∈ C
    · have hve : arcEdge (u,v) hn = e := Subtype.ext (by simpa [arcEdge] using hev.symm)
      have hp : (u,v) ∈ orientedArcs M C := mem_orientedArcs.mpr
        ⟨huC,hsides.mp huC,hn,hve.symm ▸ he⟩
      exact mem_arcGraph.mpr ⟨(u,v),hp,hn,hve⟩
    · have hvC : v ∈ C := by by_contra h; exact huC (hsides.mpr h)
      have hve : arcEdge (v,u) hn.symm = e := Subtype.ext
        (by simpa [arcEdge,Finset.pair_comm] using hev.symm)
      have hp : (v,u) ∈ orientedArcs M C := mem_orientedArcs.mpr
        ⟨hvC,huC,hn.symm,hve.symm ▸ he⟩
      exact mem_arcGraph.mpr ⟨(v,u),hp,hn.symm,hve⟩

theorem arcGraph_union (F H : Finset (V × V)) : arcGraph (F ∪ H) = arcGraph F ∪ arcGraph H := by
  ext e
  simp only [mem_arcGraph,Finset.mem_union]
  constructor
  · rintro ⟨p,hp,hpn,hpe⟩
    rcases hp with hp | hp
    · exact Or.inl ⟨p,hp,hpn,hpe⟩
    · exact Or.inr ⟨p,hp,hpn,hpe⟩
  · rintro (⟨p,hp,hpn,hpe⟩ | ⟨p,hp,hpn,hpe⟩)
    · exact ⟨p,Or.inl hp,hpn,hpe⟩
    · exact ⟨p,Or.inr hp,hpn,hpe⟩

theorem arcs_union_matching {F H : Finset (V × V)}
    (hF : RobustMatching.Dual.IsMatching F) (hH : RobustMatching.Dual.IsMatching H)
    (hs : Disjoint (sourceSupport F) (sourceSupport H))
    (ht : Disjoint (targetSupport F) (targetSupport H)) :
    RobustMatching.Dual.IsMatching (F ∪ H) := by
  constructor
  · intro p hp q hq he
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · exact hF.1 hp hq he
    · exact (Finset.disjoint_left.mp hs (Finset.mem_image_of_mem Prod.fst hp)
        (he.symm ▸ Finset.mem_image_of_mem Prod.fst hq)).elim
    · exact (Finset.disjoint_left.mp hs (Finset.mem_image_of_mem Prod.fst hq)
        (he ▸ Finset.mem_image_of_mem Prod.fst hp)).elim
    · exact hH.1 hp hq he
  · intro p hp q hq he
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · exact hF.2 hp hq he
    · exact (Finset.disjoint_left.mp ht (Finset.mem_image_of_mem Prod.snd hp)
        (he.symm ▸ Finset.mem_image_of_mem Prod.snd hq)).elim
    · exact (Finset.disjoint_left.mp ht (Finset.mem_image_of_mem Prod.snd hq)
        (he ▸ Finset.mem_image_of_mem Prod.snd hp)).elim
    · exact hH.2 hp hq he

theorem orientedArcs_weight (M : Graph V) (C : Finset V) (hm : Matching M)
    (hc : Crosses M C) (w : Edge V → ℝ) :
    (∑ p ∈ orientedArcs M C, arcWeight w p) = ∑ e ∈ M, w e := by
  have hs : ∀ p ∈ orientedArcs M C, p.1 ∈ C ∧ p.2 ∉ C :=
    fun p hp => ⟨(mem_orientedArcs.mp hp).1,(mem_orientedArcs.mp hp).2.1⟩
  have hh := same_side_arcs_weight (orientedArcs M C) C (orientedArcs_matching M C hm) hs w
  rw [arcGraph_orientedArcs M C hc] at hh
  exact hh.symm

/-- Every actual admissible pair is realized by an actual even partial
permutation avoiding the marked columns, with every weight sum preserved. -/
theorem admissible_to_evenFactor (P Q : Graph V) (marks : Finset V)
    (ha : Admissible P Q marks) :
    ∃ F : Finset (V × V), EvenFactor F ∧ Disjoint (targetSupport F) marks ∧
      arcGraph F = P ∪ Q ∧
      ∀ w : Edge V → ℝ, (∑ p ∈ F, arcWeight w p) = pairWeight w (P,Q) := by
  obtain ⟨C,hC⟩ := matching_union_exists_crosses P Q ha.1 ha.2.1
  obtain ⟨D,hD,hdm⟩ := orient_cut_away_from_marks (P ∪ Q) C marks hC
    (admissible_union_separated ha)
  let F₁ := orientedArcs P D
  let F₂ := orientedArcs Q (Finset.univ \ D)
  let F := F₁ ∪ F₂
  have hs₁ : ∀ p ∈ F₁, p.1 ∈ D ∧ p.2 ∉ D :=
    fun p hp => ⟨(mem_orientedArcs.mp hp).1,(mem_orientedArcs.mp hp).2.1⟩
  have hs₂ : ∀ p ∈ F₂, p.1 ∉ D ∧ p.2 ∈ D := by
    intro p hp
    have hh := mem_orientedArcs.mp hp
    simpa using And.intro hh.1 hh.2.1
  have hsrc : Disjoint (sourceSupport F₁) (sourceSupport F₂) := by
    apply Finset.disjoint_left.mpr
    intro v hv₁ hv₂
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv₁
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hv₂
    exact (hs₂ q hq).1 (hqp.symm ▸ (hs₁ p hp).1)
  have htgt : Disjoint (targetSupport F₁) (targetSupport F₂) := by
    apply Finset.disjoint_left.mpr
    intro v hv₁ hv₂
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv₁
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hv₂
    exact (hs₁ p hp).2 (hqp ▸ (hs₂ q hq).2)
  have hdis : Disjoint F₁ F₂ := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (hs₂ p hq).1 (hs₁ p hp).1
  have hPD : Crosses P D := crosses_mono hD Finset.subset_union_left
  have hQD : Crosses Q (Finset.univ \ D) :=
    crosses_compl (crosses_mono hD Finset.subset_union_right)
  have hgraph : arcGraph F = P ∪ Q := by
    change arcGraph (orientedArcs P D ∪ orientedArcs Q (Finset.univ \ D)) = P ∪ Q
    rw [arcGraph_union,arcGraph_orientedArcs P D hPD,
      arcGraph_orientedArcs Q (Finset.univ \ D) hQD]
  have hloop : ∀ p ∈ F, p.1 ≠ p.2 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (mem_orientedArcs.mp hp).2.2.choose
    · exact (mem_orientedArcs.mp hp).2.2.choose
  have hfactor : EvenFactor F := by
    refine ⟨arcs_union_matching
      (orientedArcs_matching P D ha.1) (orientedArcs_matching Q (Finset.univ \ D) ha.2.1)
      hsrc htgt,hloop,?_⟩
    rw [← arcGraph_simpleGraph,hgraph]
    exact crosses_colorable hD
  have havoid : Disjoint (targetSupport F) marks := by
    apply Finset.disjoint_left.mpr
    intro v hv hm
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨_,_,hpn,hpP⟩ := mem_orientedArcs.mp hp
      exact Finset.disjoint_left.mp ha.2.2.1
        (mem_covered.mpr ⟨arcEdge p hpn,hpP,by simp [arcEdge]⟩) hm
    · exact Finset.disjoint_left.mp hdm (hs₂ p hp).2 hm
  refine ⟨F,hfactor,havoid,hgraph,?_⟩
  intro w
  rw [show F = F₁ ∪ F₂ from rfl,Finset.sum_union hdis,
    orientedArcs_weight P D ha.1 hPD w,
    orientedArcs_weight Q (Finset.univ \ D) ha.2.1 hQD w]
  rfl

end RobustMatching.R7GraphInterpretation

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphInterpretation.admissible_to_evenFactor
