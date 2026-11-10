import RobustMatching.R7GraphInterpretationPair

/-! Exact ambient-graph and unordered-edge-weight adapters for the
matching-pair / directed-factor correspondence. -/

noncomputable section
open scoped BigOperators symmDiff
open Classical

namespace RobustMatching.R7GraphInterpretation
open RobustMatching.R2Cut RobustMatching.R7GraphKonig
open RobustMatching.R7GraphComponents RobustMatching.R7AlgebraPath

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_sym2_of_edge (e : Edge V) : ∃ q : Sym2 V, q.toFinset = e.val := by
  obtain ⟨u,v,hn,he⟩ := Finset.card_eq_two.mp e.property
  exact ⟨s(u,v),by simpa only [Sym2.toFinset_mk_eq] using he.symm⟩

def edgeSym2 (e : Edge V) : Sym2 V := (exists_sym2_of_edge e).choose

theorem edgeSym2_toFinset (e : Edge V) : (edgeSym2 e).toFinset = e.val :=
  (exists_sym2_of_edge e).choose_spec

theorem edgeSym2_arcEdge (p : V × V) (hp : p.1 ≠ p.2) :
    edgeSym2 (arcEdge p hp) = s(p.1,p.2) := by
  apply sym2_toFinset_injective
  rw [edgeSym2_toFinset,Sym2.toFinset_mk_eq]
  rfl

def originalWeight (w : Sym2 V → ℕ) (e : Edge V) : ℝ := w (edgeSym2 e)

theorem arcWeight_originalWeight (w : Sym2 V → ℕ) (p : V × V) (hp : p.1 ≠ p.2) :
    arcWeight (originalWeight w) p = (w s(p.1,p.2) : ℝ) := by
  rw [arcWeight_eq _ _ hp]
  simp only [originalWeight,edgeSym2_arcEdge]

theorem factor_weight_originalWeight (w : Sym2 V → ℕ) (F : Finset (V × V))
    (hl : ∀ p ∈ F, p.1 ≠ p.2) :
    (∑ p ∈ F, arcWeight (originalWeight w) p) = (∑ p ∈ F, w s(p.1,p.2) : ℕ) := by
  simp only [Nat.cast_sum]
  exact Finset.sum_congr rfl (fun p hp => arcWeight_originalWeight w p (hl p hp))

theorem arcGraph_subset_of_adj {F : Finset (V × V)} {G : Graph V}
    (h : ∀ p ∈ F, (simpleGraph G).Adj p.1 p.2) : arcGraph F ⊆ G := by
  intro e he
  obtain ⟨p,hp,hpn,rfl⟩ := mem_arcGraph.mp he
  obtain ⟨⟨f,hf,hfe⟩,_⟩ := h p hp
  have heq : arcEdge p hpn = f := Subtype.ext (by
    simpa only [Sym2.toFinset_mk_eq,arcEdge] using hfe)
  exact heq.symm ▸ hf

theorem arcs_adj_of_arcGraph_subset {F : Finset (V × V)} {G : Graph V}
    (hloop : ∀ p ∈ F, p.1 ≠ p.2) (h : arcGraph F ⊆ G) :
    ∀ p ∈ F, (simpleGraph G).Adj p.1 p.2 := by
  intro p hp
  exact adj_of_edge (h (mem_arcGraph.mpr ⟨p,hp,hloop p hp,rfl⟩))
    (by simp [arcEdge]) (by simp [arcEdge]) (hloop p hp)

theorem evenFactor_weight_le_pathValue (w : Edge V → ℝ) (G : Graph V)
    (F : Finset (V × V)) (marks : Finset V) (hf : EvenFactor F)
    (hG : ∀ p ∈ F, (simpleGraph G).Adj p.1 p.2)
    (ha : Disjoint (targetSupport F) marks) :
    (∑ p ∈ F, arcWeight w p) ≤ pathValue w G marks := by
  obtain ⟨N₁,N₂,h₁,h₂,hadm,hw⟩ := evenFactor_to_admissible F hf marks ha
  rw [← hw w]
  exact pairWeight_le_pathValue w (h₁.trans (arcGraph_subset_of_adj hG))
    (h₂.trans (arcGraph_subset_of_adj hG)) hadm

theorem pathValue_attained_by_evenFactor (w : Edge V → ℝ) (G : Graph V)
    (marks : Finset V) :
    ∃ F : Finset (V × V), EvenFactor F ∧ Disjoint (targetSupport F) marks ∧
      (∀ p ∈ F, (simpleGraph G).Adj p.1 p.2) ∧
      pathValue w G marks = ∑ p ∈ F, arcWeight w p := by
  obtain ⟨p,hp,hval⟩ := pathValue_attained w G marks
  obtain ⟨hp₁,hp₂,hadm⟩ := (mem_feasiblePairs G marks p).mp hp
  obtain ⟨F,hF,havoid,hgraph,hwt⟩ := admissible_to_evenFactor p.1 p.2 marks hadm
  have hsub : arcGraph F ⊆ G := by
    rw [hgraph]
    exact Finset.union_subset hp₁ hp₂
  refine ⟨F,hF,havoid,arcs_adj_of_arcGraph_subset hF.loopless hsub,?_⟩
  rw [hwt w,hval]

end RobustMatching.R7GraphInterpretation

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphInterpretation.evenFactor_weight_le_pathValue
#print axioms RobustMatching.R7GraphInterpretation.pathValue_attained_by_evenFactor
