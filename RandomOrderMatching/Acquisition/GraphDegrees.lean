import RandomOrderMatching.Acquisition.Degrees

/-! Exact bridge from the acquisition's finite incidence degree to the
same graph's mathlib SimpleGraph degree. -/
noncomputable section
open Classical
namespace RandomOrderMatching.Acquisition
open RandomOrderMatching.Graph RandomOrderMatching.Graph.Konig
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem simpleGraph_degree (H : Graph V) (v : V) :
    (RandomOrderMatching.Graph.Konig.simpleGraph H).degree v = degree H v := by
  classical
  rw [←SimpleGraph.card_incidenceFinset_eq_degree]
  unfold degree
  let f : (q : Sym2 V) → q ∈ (RandomOrderMatching.Graph.Konig.simpleGraph H).incidenceFinset v → Edge V :=
    fun q hq => ⟨q.toFinset,by
      have hh := (SimpleGraph.mem_incidenceFinset _ _ _).mp hq
      obtain ⟨e,he,heq⟩ := RandomOrderMatching.Graph.Konig.mem_simpleGraph_edge hh.1
      exact heq.symm ▸ e.property⟩
  apply Finset.card_bij f
  · intro q hq
    have hh := (SimpleGraph.mem_incidenceFinset _ _ _).mp hq
    obtain ⟨e,he,heq⟩ := RandomOrderMatching.Graph.Konig.mem_simpleGraph_edge hh.1
    apply Finset.mem_filter.mpr
    constructor
    · have hfe : f q hq=e := Subtype.ext heq
      exact hfe.symm ▸ he
    · exact Sym2.mem_toFinset.mpr hh.2
  · intro q hq r hr heq
    exact RandomOrderMatching.Graph.Konig.sym2_toFinset_injective (congrArg Subtype.val heq)
  · intro e he
    obtain ⟨heH,hve⟩ := Finset.mem_filter.mp he
    obtain ⟨a,b,hab,heq⟩ := Finset.card_eq_two.mp e.property
    let q : Sym2 V := s(a,b)
    have hqval : q.toFinset=e.val := by simpa [q,Sym2.toFinset_mk_eq] using heq.symm
    have hqdiag : ¬q.IsDiag := by
      intro hd
      have hh := Sym2.card_toFinset_of_isDiag q hd
      rw [hqval,e.property] at hh
      norm_num at hh
    have hqe : q ∈ (RandomOrderMatching.Graph.Konig.simpleGraph H).edgeSet := by
      rw [RandomOrderMatching.Graph.Konig.simpleGraph,SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨⟨e,heH,hqval⟩,hqdiag⟩
    have hqi : q ∈ (RandomOrderMatching.Graph.Konig.simpleGraph H).incidenceFinset v := by
      apply (SimpleGraph.mem_incidenceFinset _ _ _).mpr
      exact ⟨hqe,Sym2.mem_toFinset.mp (hqval.symm ▸ hve)⟩
    exact ⟨q,hqi,Subtype.ext hqval⟩

end RandomOrderMatching.Acquisition
#print axioms RandomOrderMatching.Acquisition.simpleGraph_degree
