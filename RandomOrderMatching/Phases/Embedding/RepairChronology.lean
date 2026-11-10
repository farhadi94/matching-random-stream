import RandomOrderMatching.Analysis.Repair.Labeling.Parents
import RandomOrderMatching.Analysis.Repair.Labeling.Reference
import RandomOrderMatching.Phases.Execution.State

/-! Physical original-label chronology for the canonical repair partition.
Only the pointwise before/after consequences of the actual clock bracket
are inputs; no selected-parent or ordinary-support chronology is assumed. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
namespace RandomOrderMatching.Phases.Embedding
open RandomOrderMatching.Graph RandomOrderMatching.Phases.Execution RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Analysis.Repair.Labeling RandomOrderMatching.Analysis.Repair.Typed RandomOrderMatching.Analysis.Repair.Probability
variable {X V B : Type*} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
variable {q : ℕ}

theorem kind_available {C : Finset X} {available : Graph X} {e : Edge X}
    (hk : actualPairKind C available e=.gate ∨ actualPairKind C available e=.internalAvailable) :
    e∈available := by
  unfold actualPairKind at hk
  split_ifs at hk <;> simp_all

variable (Mc : Graph X) (hm : Matching Mc) (C : Finset X) (available : Graph X)
  (bin : X→Fin q) (mask : X→Fin 4)
local notation "D" => coordinatesFromMatching Mc hm C available bin mask
local notation "lab" => actualVertexEquiv Mc hm C available bin mask

/-- An actual typed gate is its own available benchmark edge. -/
theorem actual_gate_edge
    (s : States (PairFiber D .gate) (PairFiber D .missing)
      (PairFiber D .internalMissing) (PairFiber D .root))
    {c : CanonicalCenters D} {x : CanonicalOutsides D} (hg : gateRelation s c x) :
    ∃g : PairFiber D .gate, s.active g=true ∧
      @mapEdge _ _ (Classical.decEq _) (inferInstance : DecidableEq X) lab (lab).injective (RandomOrderMatching.Graph.BipartiteMatrix.edgeOf (c,x))=g.val.val := by
  rcases c with g|m|p|i|j <;> rcases x with r|m'|g'|u <;>
    simp only [gateRelation] at hg
  obtain ⟨rfl,ha⟩ := hg
  refine ⟨g,ha,?_⟩
  exact actual_benchmark_edge Mc hm C available bin mask (.inr (.inl g))

/-- The ordinary repair graph consists only of actual reference edges and
active available benchmark gates. -/
theorem actual_ordinary_subset (Hc : Graph X)
    (s : States (PairFiber D .gate) (PairFiber D .missing)
      (PairFiber D .internalMissing) (PairFiber D .root)) :
    @mapGraph _ _ (Classical.decEq _) (inferInstance : DecidableEq X) lab (lab).injective
      (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges fun c x =>
        actualReferenceAdj Mc hm C available bin mask Hc c x ∨ gateRelation s c x)⊆Hc∪Mc := by
  intro e he
  simp only [mapGraph,Finset.mem_image] at he
  obtain ⟨f,hf,rfl⟩ := he
  simp only [RandomOrderMatching.Graph.BipartiteMatrix.graphEdges,RandomOrderMatching.Graph.BipartiteMatrix.pairs,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and] at hf
  obtain ⟨p,hp,rfl⟩ := hf
  rcases hp with hr|hg
  · exact Finset.mem_union_left _ hr
  · obtain ⟨g,_,hg⟩ := actual_gate_edge Mc hm C available bin mask s hg
    rw [hg]
    exact Finset.mem_union_right _ g.val.property

variable (parent : Edge X→Edge V) (original : B→Edge V) (par : Mc→B)
  (hpar : ∀e:Mc,parent e.val=original (par e))
  (H0 : Graph V) (eligible : Edge V→Prop) (stream : List (Edge V))
  (z : B→Clock)
local notation "s" => states (fiberParents D par) z

/-- Available original parents belong to the full shared base. -/
theorem available_parent_shared
    (hav : ∀e∈available,parent e∈H0 ∨ (eligible (parent e) ∧ parent e∈stream))
    {e : Edge X} (he : e∈available) : parent e∈sharedBase H0 eligible stream := by
  rcases hav e he with hh | ⟨hel,hmem⟩
  · exact Finset.mem_union_left _ hh
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨by simpa [List.take_length] using hmem,hel⟩

include hpar

/-- Reference parents are frozen and active physical gates are seen before a.
This derives the full ordinary-support initialization obligation. -/
theorem typed_ordinary_initial (Hc : Graph X) (a : ℕ)
    (href : ∀e∈Hc,parent e∈H0)
    (hav : ∀e∈available,parent e∈H0 ∨ (eligible (parent e) ∧ parent e∈stream))
    (hbefore : ∀b,activeBit (z b)=true→ original b∈stream.take a) :
    ∀e∈@mapGraph _ _ (Classical.decEq _) (inferInstance : DecidableEq X) lab (lab).injective
      (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges fun c x =>
        actualReferenceAdj Mc hm C available bin mask Hc c x ∨ gateRelation s c x),
      parent e∈initial H0 eligible stream a := by
  intro e he
  simp only [mapGraph,Finset.mem_image] at he
  obtain ⟨f,hf,rfl⟩ := he
  simp only [RandomOrderMatching.Graph.BipartiteMatrix.graphEdges,RandomOrderMatching.Graph.BipartiteMatrix.pairs,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and] at hf
  obtain ⟨p,hp,rfl⟩ := hf
  rcases hp with hr|hg
  · exact Finset.mem_union_left _ (href _ hr)
  · obtain ⟨g,ha,hg⟩ := actual_gate_edge Mc hm C available bin mask s hg
    rw [hg]
    have hga : g.val.val∈available := kind_available (Or.inl g.property)
    rcases hav _ hga with hh|⟨hel,_⟩
    · exact Finset.mem_union_left _ hh
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨?_,hel⟩
      apply List.mem_toFinset.mpr
      rw [hpar g.val]
      exact hbefore (par g.val) ha

/-- All selected parents are either in the actual full shared base, or are
physical late labels. This includes internal available pairs at every clock. -/
theorem typed_selected_chronology (t : ℕ)
    (hav : ∀e∈available,parent e∈H0 ∨ (eligible (parent e) ∧ parent e∈stream))
    (hafter : ∀b,earlyBit (z b)=false→ original b∈stream.drop t) :
    ∀e∈@mapGraph _ _ (Classical.decEq _) (inferInstance : DecidableEq X) lab (lab).injective
      (selectedEdges (P:=CenterUnmatched D) (I:=PairFiber D .internalAvailable)
        (U:=OutsideUnmatched D) s),
      parent e∈sharedBase H0 eligible stream ∨ parent e∈stream.drop t := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  simp only [selectedEdges,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and] at hf
  obtain ⟨b,hs,rfl⟩ := hf
  rw [actual_benchmark_edge]
  rcases b with r|g|m|i|j
  · apply Or.inr
    rw [hpar]
    exact hafter (par r.val) hs
  · apply Or.inl
    exact available_parent_shared available parent H0 eligible stream hav
      (kind_available (Or.inl g.property))
  · apply Or.inr
    rw [hpar]
    exact hafter (par m.val) hs
  · apply Or.inl
    exact available_parent_shared available parent H0 eligible stream hav
      (kind_available (Or.inr i.property))
  · apply Or.inr
    rw [hpar]
    exact hafter (par j.val) hs

end RandomOrderMatching.Phases.Embedding
