import RandomOrderMatching.Analysis.Repair.Typed.Benchmark

/-! The endpoints deleted by the typed support construction are exactly
the endpoints of its actual selected matching, on the designated cut
side. Thus `deletionAdj` denotes genuine vertex-deleted graphs. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RandomOrderMatching.Analysis.Repair.Typed

variable {G M P I J R U : Type*}
variable [Fintype G] [Fintype M] [Fintype P] [Fintype I]
  [Fintype J] [Fintype R] [Fintype U]

def vertexSelected (s : States G M J R) :
    Centers G M P I J ⊕ Outsides R M G U → Prop :=
  Sum.elim (centerSelected s) (outsideSelected s)

lemma endpoint_selected_iff (s : States G M J R)
    (b : Benchmarks R G M I J) (t : Bool) :
    vertexSelected s (endpoint (P := P) (U := U) b t) ↔ selectedBench s b := by
  rcases b with r | g | m | i | j <;> cases t <;>
    simp [endpoint, vertexSelected, centerSelected, outsideSelected, selectedBench]

lemma selected_endpoint_exists (s : States G M J R)
    (v : Centers G M P I J ⊕ Outsides R M G U) (hv : vertexSelected s v) :
    ∃ (b : Benchmarks R G M I J) (t : Bool),
      selectedBench s b ∧ endpoint (P := P) (U := U) b t = v := by
  rcases v with c | x
  · rcases c with g | m | p | ⟨i,t⟩ | ⟨j,t⟩
    · exact ⟨.inr (.inl g), false, hv, rfl⟩
    · exact ⟨.inr (.inr (.inl m)), false, hv, rfl⟩
    · exact False.elim hv
    · exact ⟨.inr (.inr (.inr (.inl i))), t, trivial, rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr j))), t, hv, rfl⟩
  · rcases x with ⟨r,t⟩ | m | g | u
    · exact ⟨.inl r, t, hv, rfl⟩
    · exact ⟨.inr (.inr (.inl m)), true, hv, rfl⟩
    · exact ⟨.inr (.inl g), true, hv, rfl⟩
    · exact False.elim hv

theorem selected_covered_iff (s : States G M J R)
    (v : Centers G M P I J ⊕ Outsides R M G U) :
    v ∈ RandomOrderMatching.Graph.covered (selectedEdges (P := P) (I := I) (U := U) s) ↔
      vertexSelected s v := by
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := RandomOrderMatching.Graph.mem_covered.mp hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    have hsel := (Finset.mem_filter.mp hb).2
    simp only [benchmarkEdge, Finset.mem_insert, Finset.mem_singleton] at hve
    rcases hve with rfl | rfl
    · exact (endpoint_selected_iff s b false).mpr hsel
    · exact (endpoint_selected_iff s b true).mpr hsel
  · intro hv
    obtain ⟨b, t, hb, rfl⟩ := selected_endpoint_exists s v hv
    apply RandomOrderMatching.Graph.mem_covered.mpr
    refine ⟨benchmarkEdge b, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩
    · cases t <;> simp [benchmarkEdge]

def deletionVertices (s : States G M J R)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (layer : Bool) : Finset (Centers G M P I J ⊕ Outsides R M G U) :=
  Finset.univ.filter fun v => vertexSelected s v ∧ Sum.elim sideC sideO v = layer

theorem deletionVertices_eq_selected (s : States G M J R)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (layer : Bool) :
    deletionVertices s sideC sideO layer =
      (RandomOrderMatching.Graph.covered (selectedEdges (P := P) (I := I) (U := U) s)).filter
        (fun v => Sum.elim sideC sideO v = layer) := by
  ext v
  simp only [deletionVertices, Finset.mem_filter, Finset.mem_univ,
    true_and, selected_covered_iff]

lemma edge_disjoint_deletion (s : States G M J R)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (layer : Bool) (c : Centers G M P I J) (x : Outsides R M G U) :
    Disjoint (RandomOrderMatching.Graph.BipartiteMatrix.edgeOf (c,x)).val (deletionVertices s sideC sideO layer) ↔
      centerSurvives s sideC layer c ∧ outsideSurvives s sideO layer x := by
  constructor
  · intro h
    constructor
    · intro hc
      have he : Sum.inl c ∈ (RandomOrderMatching.Graph.BipartiteMatrix.edgeOf (c,x)).val := by
        simp [RandomOrderMatching.Graph.BipartiteMatrix.edgeOf]
      have hd : Sum.inl c ∈ deletionVertices s sideC sideO layer :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      exact (Finset.disjoint_left.mp h) he hd
    · intro hx
      have he : Sum.inr x ∈ (RandomOrderMatching.Graph.BipartiteMatrix.edgeOf (c,x)).val := by
        simp [RandomOrderMatching.Graph.BipartiteMatrix.edgeOf]
      have hd : Sum.inr x ∈ deletionVertices s sideC sideO layer :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      exact (Finset.disjoint_left.mp h) he hd
  · intro h
    apply Finset.disjoint_left.mpr
    intro v hv hd
    have hh := (Finset.mem_filter.mp hd).2
    simp only [RandomOrderMatching.Graph.BipartiteMatrix.edgeOf, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h.1 hh
    · exact h.2 hh

/-- Equality with the ordinary graph filtered by actual deleted vertices,
not just an abstract adjacency predicate with a suggestive name. -/
theorem deletion_graph_eq (s : States G M J R)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (layer : Bool) :
    RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s H sideC sideO layer) =
      (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (fun c x => H c x ∨ gateRelation s c x)).filter
        (fun e => Disjoint e.val (deletionVertices s sideC sideO layer)) := by
  ext e
  simp only [RandomOrderMatching.Graph.BipartiteMatrix.graphEdges, RandomOrderMatching.Graph.BipartiteMatrix.pairs, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro he
    obtain ⟨⟨c,x⟩, hh, rfl⟩ := he
    exact ⟨⟨(c,x), hh.1, rfl⟩,
      (edge_disjoint_deletion s sideC sideO layer c x).mpr hh.2⟩
  · intro he
    obtain ⟨⟨⟨c,x⟩, hh, rfl⟩, hd⟩ := he
    have hs := (edge_disjoint_deletion s sideC sideO layer c x).mp hd
    exact ⟨(c,x), ⟨hh, hs⟩, rfl⟩

end RandomOrderMatching.Analysis.Repair.Typed
