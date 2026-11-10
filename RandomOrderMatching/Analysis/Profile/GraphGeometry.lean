import RandomOrderMatching.Analysis.Profile.DegreeBins

noncomputable section
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Graph RandomOrderMatching.Certificates.DegreeProfile

def vertexLower {q} (data : ProfileData q) : Column q → ℚ
  | .center c => lower data c.1
  | .outside x => lower data x.1
  | _ => 0

theorem vertexLower_bin {B U : Type*} {q} (data : ProfileData q) (d : Coordinates B U q)
    (v : Vertex B U) : vertexLower data (vertexColumn d v)=lower data (d.bin v) := by
  have hv := vertexColumn_is_vertex d v
  cases h : vertexColumn d v <;> simp [h,IsVertexColumn] at hv
  · rename_i c
    simp only [vertexLower,vertex_center_bin d v c h]
  · rename_i x
    simp only [vertexLower,vertex_outside_bin d v x h]

theorem referenceColumn_allowed {q} (data : ProfileData q) (u v : Column q)
    (huv : IsVertexColumn u) (hvv : IsVertexColumn v)
    (hu : columnAllowed data u) (hv : columnAllowed data v)
    (hc : IsCenterColumn u ∨ IsCenterColumn v)
    (hs : vertexLower data u+vertexLower data v ≤ 1) :
    columnAllowed data (referenceColumn u v) := by
  cases u <;> cases v <;> simp [IsVertexColumn,IsCenterColumn] at huv hvv hc
  · rename_i c d
    dsimp only [referenceColumn]
    split_ifs with h
    · exact ⟨h,hs⟩
    · exact ⟨le_of_not_ge h,by simpa only [vertexLower,add_comm] using hs⟩
  · exact ⟨hv,hs⟩
  · exact ⟨hu,by simpa only [vertexLower,add_comm] using hs⟩

section Actual
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree assumptions are on the actual simple graph and actual
benchmark edges. The only mask premise is pointwise outside admissibility;
it is discharged separately by the minimum-load mask construction. -/
theorem actual_profile_geometry
    (M H : Graph V) (hM : Matching M) (C : Finset V) (available : Graph V)
    (bin : V → Fin 152) (mask : V → Fin 4) (beta : ℝ) (hbeta : 0 < beta)
    (hcover : ∀ e∈H, ∃ v∈e.val, v∈C)
    (hbin : ∀ v, beta*(lower Concrete.data (bin v) : ℝ) ≤ incidenceDegree H v ∧
      incidenceDegree H v ≤ beta*(upper Concrete.data (bin v) : ℝ))
    (hvertex : ∀ v, columnAllowed Concrete.data
      (vertexColumn (coordinatesFromMatching M hM C available bin mask) v))
    (hedge : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta)
    (hpairLower : ∀ e∈M, actualPairKind C available e=.root ∨
      actualPairKind C available e=.missing ∨ actualPairKind C available e=.internalMissing →
      beta*(1-(Concrete.data.lam : ℝ)) ≤ incidenceDegree H (orientedEndpoint C e 0)+
        incidenceDegree H (orientedEndpoint C e 1))
    (hpairUpper : ∀ e∈M, actualPairKind C available e=.internalAvailable →
      incidenceDegree H (orientedEndpoint C e 0)+incidenceDegree H (orientedEndpoint C e 1) ≤ beta) :
    ProfileGeometry (coordinatesFromMatching M hM C available bin mask)
      (actualReference M H hM C available bin mask)
      (actualLeft M H hM C) (actualRight M H hM C) Concrete.data beta := by
  let d := coordinatesFromMatching M hM C available bin mask
  let iso := coveredMatchingCoordinateEquiv M hM C
  have hlo (v : MatchingVertex M) : beta*(lower Concrete.data (d.bin v) : ℝ) ≤
      endpointDegree (actualLeft M H hM C) (actualRight M H hM C) v := by
    rw [actual_endpoint_degree]
    exact (hbin (iso v)).1
  have hhi (v : MatchingVertex M) : endpointDegree (actualLeft M H hM C) (actualRight M H hM C) v ≤
      beta*(upper Concrete.data (d.bin v) : ℝ) := by
    rw [actual_endpoint_degree]
    exact (hbin (iso v)).2
  have hpair (i : M) (hk : d.kind i=.root ∨ d.kind i=.missing ∨ d.kind i=.internalMissing) :
      beta*(1-(Concrete.data.lam : ℝ)) ≤
        endpointDegree (actualLeft M H hM C) (actualRight M H hM C) (.inl (i,0))+
        endpointDegree (actualLeft M H hM C) (actualRight M H hM C) (.inl (i,1)) := by
    simp only [actual_endpoint_degree,coveredMatchingCoordinateEquiv_pair]
    exact hpairLower i.val i.property hk
  refine {
    compatible := actual_reference_compatible M H hM C available bin mask hcover
    vertex_allowed := hvertex
    benchmark_allowed := ?_
    reference_allowed := ?_
    center_lower := ?_
    center_upper := ?_
    outside_lower := ?_
    outside_upper := ?_
    center_degree := ?_
    positive_degree := ?_
    root_degree := fun i hi => hpair i (Or.inl hi)
    missing_degree := fun i hi => hpair i (Or.inr (Or.inl hi)) }
  · apply benchmark_allowed_of_bins d Concrete.data hvertex
    · intro i hi
      apply bin_pair_upper hbeta (hlo (.inl (i,0))) (hlo (.inl (i,1)))
      simp only [actual_endpoint_degree,coveredMatchingCoordinateEquiv_pair]
      exact hpairUpper i.val i.property hi
    · intro i hi
      exact bin_pair_lower hbeta (hhi (.inl (i,0))) (hhi (.inl (i,1))) (hpair i hi)
  · intro e
    apply referenceColumn_allowed Concrete.data _ _ (vertexColumn_is_vertex d _) (vertexColumn_is_vertex d _)
      (hvertex _) (hvertex _)
    · have hh := actual_reference_compatible M H hM C available bin mask hcover e
      rcases hh with ⟨c,f,hc,hf,_⟩ | ⟨c,x,hc,hx,_⟩ | ⟨c,x,hc,hx,_⟩
      · exact Or.inl (by simp [d,hc,IsCenterColumn])
      · exact Or.inl (by simp [d,hc,IsCenterColumn])
      · exact Or.inr (by simp [d,hc,IsCenterColumn])
    · rw [vertexLower_bin,vertexLower_bin]
      apply bin_pair_upper hbeta (hlo _) (hlo _)
      simp only [actual_endpoint_degree,actualLeft,actualRight,Equiv.apply_symm_apply]
      exact hedge e.val e.property
  · intro c v hv
    rw [vertex_center_bin d v c hv]
    exact hlo v
  · intro c v hv
    rw [vertex_center_bin d v c hv]
    exact hhi v
  · intro x v hv
    rw [vertex_outside_bin d v x hv]
    exact hlo v
  · intro x v hv
    rw [vertex_outside_bin d v x hv]
    exact hhi v
  · intro v _
    have htop : (upper Concrete.data (d.bin v) : ℝ) ≤ 1 := by
      exact_mod_cast concrete_upper_le_one (d.bin v)
    exact (hhi v).trans (by nlinarith)
  · intro v hv
    change PositiveOutside (vertexColumn d v) at hv
    have hv0 : (d.bin v).val ≠ 0 := by
      cases hc : vertexColumn d v <;> simp [hc,PositiveOutside] at hv
      rename_i x
      have hx := vertex_outside_bin d v x hc
      intro hz
      apply hv.2
      apply Fin.ext
      simpa only [hx,Fin.val_zero] using hz
    have hpos : (1/256 : ℝ) ≤ (lower Concrete.data (d.bin v) : ℝ) := by
      have hp := (Rat.cast_le (K := ℝ)).mpr (concrete_positive_bin (d.bin v) hv0)
      norm_num at hp
      exact hp
    exact (show beta/256 ≤ beta*(lower Concrete.data (d.bin v) : ℝ) by nlinarith).trans (hlo v)

end Actual
end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.actual_profile_geometry
