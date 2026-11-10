import RandomOrderMatching.Analysis.Repair.Labeling.Reference
import RandomOrderMatching.Analysis.Profile.GraphIncidence

/-! Actual crossing reference edges correspond bijectively to canonical
center/outside incidence pairs. This proves the exact sum identity used
by the finite LP objective, without a multiplicity assumption. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Classical

namespace RandomOrderMatching.Analysis.Repair.Labeling
open RandomOrderMatching.Analysis.Profile RandomOrderMatching.Graph
open RandomOrderMatching.Phases.Execution RandomOrderMatching.Graph.BipartiteMatrix

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
variable (M0 : Graph V) (hM : Matching M0) (C : Finset V) (available : Graph V)
  (bin : V → Fin q) (mask : V → Fin 4)

local notation "D" => coordinatesFromMatching M0 hM C available bin mask

def actualCrossEdges (H : Graph V) : Graph V :=
  H.filter fun e => (e.val ∩ C).card = 1

theorem actual_reference_crosses (c : CanonicalCenters D) (x : CanonicalOutsides D) :
    ((actualReferenceEdge M0 hM C available bin mask c x).val ∩ C).card = 1 := by
  rw [actual_reference_endpoints]
  have hc := actual_center_mem M0 hM C available bin mask c
  have hx := actual_outside_not_mem M0 hM C available bin mask x
  have heq :
      ({actualVertexEquiv M0 hM C available bin mask (.inl c),
        actualVertexEquiv M0 hM C available bin mask (.inr x)} ∩ C) =
      {actualVertexEquiv M0 hM C available bin mask (.inl c)} := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    grind
  rw [heq]
  simp

theorem actual_reference_pair_injective : Function.Injective
    (fun p : CanonicalCenters D × CanonicalOutsides D =>
      actualReferenceEdge M0 hM C available bin mask p.1 p.2) := by
  intro p r h
  apply edgeOf_injective
  exact mapEdge_injective (actualVertexEquiv M0 hM C available bin mask)
    (actualVertexEquiv M0 hM C available bin mask).injective h

theorem actual_reference_oriented_endpoints
    (c : CanonicalCenters D) (x : CanonicalOutsides D) :
    orientedEndpoint C (actualReferenceEdge M0 hM C available bin mask c x) 0 =
      actualVertexEquiv M0 hM C available bin mask (.inl c) ∧
    orientedEndpoint C (actualReferenceEdge M0 hM C available bin mask c x) 1 =
      actualVertexEquiv M0 hM C available bin mask (.inr x) := by
  have h0 := orientedEndpoint_mem C (actualReferenceEdge M0 hM C available bin mask c x) 0
  have h1 := orientedEndpoint_mem C (actualReferenceEdge M0 hM C available bin mask c x) 1
  rw [actual_reference_endpoints] at h0 h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1
  have hfirst := oriented_center_first C (actualReferenceEdge M0 hM C available bin mask c x)
  have hc := actual_center_mem M0 hM C available bin mask c
  have hx := actual_outside_not_mem M0 hM C available bin mask x
  have hne : orientedEndpoint C (actualReferenceEdge M0 hM C available bin mask c x) 0 ≠
      orientedEndpoint C (actualReferenceEdge M0 hM C available bin mask c x) 1 := by
    intro hh
    have hi := orientedEndpoint_injective C _ hh
    norm_num at hi
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact False.elim (hne (h0.trans h1.symm))
  · exact ⟨h0,h1⟩
  · exact False.elim (hx (h0 ▸ hfirst (h1.symm ▸ hc)))
  · exact False.elim (hne (h0.trans h1.symm))

theorem actual_cross_edge_has_pair (e : Edge V) (he : (e.val ∩ C).card = 1) :
    ∃ p : CanonicalCenters D × CanonicalOutsides D,
      actualReferenceEdge M0 hM C available bin mask p.1 p.2 = e := by
  have ordered : ∃ u v, u ∈ C ∧ v ∉ C ∧ e.val = {u,v} := by
    obtain ⟨u,v,hne,huv⟩ := Finset.card_eq_two.mp e.property
    by_cases hu : u ∈ C <;> by_cases hv : v ∈ C
    · have hi : e.val ∩ C = e.val := by
        rw [huv]
        apply Finset.inter_eq_left.mpr
        intro x hx
        rcases (show x = u ∨ x = v by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx) with rfl | rfl
        · exact hu
        · exact hv
      rw [hi,e.property] at he
      norm_num at he
    · exact ⟨u,v,hu,hv,huv⟩
    · exact ⟨v,u,hv,hu,by simpa [Finset.pair_comm] using huv⟩
    · have hi : e.val ∩ C = ∅ := by
        rw [huv]
        ext x
        constructor
        · intro hx
          obtain ⟨hx,hc⟩ := Finset.mem_inter.mp hx
          rcases (show x = u ∨ x = v by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx) with rfl | rfl
          · exact False.elim (hu hc)
          · exact False.elim (hv hc)
        · intro hx
          exact False.elim (Finset.notMem_empty _ hx)
      rw [hi] at he
      norm_num at he
  obtain ⟨u,v,hu,hv,hev⟩ := ordered
  let c := (actualCoverEquiv M0 hM C available bin mask).symm ⟨u,hu⟩
  let x := (actualOutsideEquiv M0 hM C available bin mask).symm ⟨v,hv⟩
  have hc : actualVertexEquiv M0 hM C available bin mask (.inl c) = u :=
    congrArg Subtype.val ((actualCoverEquiv M0 hM C available bin mask).apply_symm_apply ⟨u,hu⟩)
  have hx : actualVertexEquiv M0 hM C available bin mask (.inr x) = v :=
    congrArg Subtype.val ((actualOutsideEquiv M0 hM C available bin mask).apply_symm_apply ⟨v,hv⟩)
  refine ⟨(c,x),Subtype.ext ?_⟩
  rw [actual_reference_endpoints,hc,hx,hev]

abbrev ActualReferencePairs (H : Graph V) :=
  {p : CanonicalCenters D × CanonicalOutsides D //
    actualReferenceAdj M0 hM C available bin mask H p.1 p.2}

/-- The edge side is exactly the actual graph filtered by having one
endpoint in C; the pair side is exactly actual reference adjacency. -/
def actualReferencePairEquiv (H : Graph V) :
    ActualReferencePairs M0 hM C available bin mask H ≃ actualCrossEdges C H :=
  Equiv.ofBijective
    (fun p => ⟨actualReferenceEdge M0 hM C available bin mask p.val.1 p.val.2,
      Finset.mem_filter.mpr ⟨p.property,
        actual_reference_crosses M0 hM C available bin mask p.val.1 p.val.2⟩⟩) (by
      constructor
      · intro p r h
        apply Subtype.ext
        exact actual_reference_pair_injective M0 hM C available bin mask
          (congrArg Subtype.val h)
      · intro e
        obtain ⟨p,hp⟩ := actual_cross_edge_has_pair M0 hM C available bin mask e.val
          (Finset.mem_filter.mp e.property).2
        refine ⟨⟨p,?_⟩,Subtype.ext hp⟩
        change actualReferenceEdge M0 hM C available bin mask p.1 p.2 ∈ H
        rw [hp]
        exact (Finset.mem_filter.mp e.property).1)

theorem actual_reference_pair_equiv_edge (H : Graph V)
    (p : ActualReferencePairs M0 hM C available bin mask H) :
    (actualReferencePairEquiv M0 hM C available bin mask H p).val =
      actualReferenceEdge M0 hM C available bin mask p.val.1 p.val.2 := rfl

theorem actual_reference_sum (H : Graph V)
    (f : CanonicalCenters D → CanonicalOutsides D → ℝ) :
    (∑ e : actualCrossEdges C H,
      f ((actualReferencePairEquiv M0 hM C available bin mask H).symm e).val.1
        ((actualReferencePairEquiv M0 hM C available bin mask H).symm e).val.2) =
      ∑ c, ∑ x, if actualReferenceAdj M0 hM C available bin mask H c x then f c x else 0 := by
  let E := actualReferencePairEquiv M0 hM C available bin mask H
  calc
    _ = ∑ p : ActualReferencePairs M0 hM C available bin mask H, f p.val.1 p.val.2 := by
      symm
      simpa only [Equiv.symm_apply_apply] using E.sum_comp (fun e => f (E.symm e).val.1 (E.symm e).val.2)
    _ = ∑ p : CanonicalCenters D × CanonicalOutsides D,
        if actualReferenceAdj M0 hM C available bin mask H p.1 p.2 then f p.1 p.2 else 0 := by
      symm
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by intro p; simp) _
    _ = _ := Fintype.sum_prod_type _

end RandomOrderMatching.Analysis.Repair.Labeling
