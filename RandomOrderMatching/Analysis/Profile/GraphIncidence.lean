import RandomOrderMatching.Analysis.Profile.Admissibility

/-! The reference-edge records are extracted from an actual simple graph.
Their endpoint degree is proved equal to the graph's actual degree. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Graph RandomOrderMatching.Certificates.DegreeProfile

def referenceColumn {q} : Column q → Column q → Column q
  | .center c, .center d =>
      if centerIndex c ≤ centerIndex d then .internal c d else .internal d c
  | .center c, .outside x => .cross c x
  | .outside x, .center c => .cross c x
  | _, _ => .z

theorem referenceColumn_compatible {q} (u v : Column q)
    (hu : IsVertexColumn u) (hv : IsVertexColumn v)
    (hc : IsCenterColumn u ∨ IsCenterColumn v) :
    ReferenceCompatible u v (referenceColumn u v) := by
  cases u <;> cases v <;> simp [IsVertexColumn,IsCenterColumn] at hu hv hc
  · rename_i c d
    dsimp only [referenceColumn]
    split_ifs <;> exact Or.inl ⟨c,d,rfl,rfl,by simp_all⟩
  · rename_i c x
    exact Or.inr (Or.inl ⟨c,x,rfl,rfl,rfl⟩)
  · rename_i x c
    exact Or.inr (Or.inr ⟨c,x,rfl,rfl,rfl⟩)

theorem referenceColumn_order {q} (u v : Column q) (c d : CenterClass q)
    (h : referenceColumn u v=.internal c d) : centerIndex c ≤ centerIndex d := by
  cases u <;> cases v <;> simp [referenceColumn] at h
  split_ifs at h <;> rcases h with ⟨rfl,rfl⟩ <;> omega

section Actual
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem orientedEndpoint_mem (C : Finset V) (e : Edge V) (i : Fin 2) :
    orientedEndpoint C e i ∈ e.val := endpoint_mem _ _

theorem orientedEndpoint_injective (C : Finset V) (e : Edge V) :
    Function.Injective (orientedEndpoint C e) :=
  (endpoint_injective e).comp (coverOrder C e).injective

theorem orientedEndpoint_surjective (C : Finset V) (e : Edge V) (v : V) (hv : v∈e.val) :
    ∃ i, orientedEndpoint C e i=v := by
  obtain ⟨j,hj⟩ := endpoint_surjective e v hv
  exact ⟨(coverOrder C e).symm j,by simpa [orientedEndpoint] using hj⟩

theorem oriented_endpoint_indicator (C : Finset V) (e : Edge V) (v : V) :
    ((if orientedEndpoint C e 0=v then 1 else 0)+
      (if orientedEndpoint C e 1=v then 1 else 0) : ℝ)=
      if v∈e.val then 1 else 0 := by
  have hne : orientedEndpoint C e 0 ≠ orientedEndpoint C e 1 := by
    intro hh
    have := orientedEndpoint_injective C e hh
    norm_num at this
  by_cases hv : v∈e.val
  · obtain ⟨i,rfl⟩ := orientedEndpoint_surjective C e v hv
    fin_cases i <;> simp [orientedEndpoint_mem,hne,hne.symm]
  · have h0 : orientedEndpoint C e 0 ≠ v := by
      intro hh; exact hv (hh ▸ orientedEndpoint_mem C e 0)
    have h1 : orientedEndpoint C e 1 ≠ v := by
      intro hh; exact hv (hh ▸ orientedEndpoint_mem C e 1)
    simp [h0,h1,hv]

def actualLeft (M H : Graph V) (hM : Matching M) (C : Finset V) : H → MatchingVertex M :=
  fun e => (coveredMatchingCoordinateEquiv M hM C).symm (orientedEndpoint C e.val 0)
def actualRight (M H : Graph V) (hM : Matching M) (C : Finset V) : H → MatchingVertex M :=
  fun e => (coveredMatchingCoordinateEquiv M hM C).symm (orientedEndpoint C e.val 1)

theorem actual_endpoint_degree (M H : Graph V) (hM : Matching M) (C : Finset V)
    (v : MatchingVertex M) :
    endpointDegree (actualLeft M H hM C) (actualRight M H hM C) v =
      incidenceDegree H (coveredMatchingCoordinateEquiv M hM C v) := by
  unfold endpointDegree incidenceDegree
  rw [←Finset.sum_coe_sort H]
  apply Finset.sum_congr rfl
  intro e _
  have h0 : actualLeft M H hM C e=v ↔
      orientedEndpoint C e.val 0=coveredMatchingCoordinateEquiv M hM C v := by
    exact Equiv.symm_apply_eq _
  have h1 : actualRight M H hM C e=v ↔
      orientedEndpoint C e.val 1=coveredMatchingCoordinateEquiv M hM C v := by
    exact Equiv.symm_apply_eq _
  simp only [h0,h1]
  exact oriented_endpoint_indicator C e.val _

def actualReference {q} (M H : Graph V) (hM : Matching M) (C : Finset V)
    (available : Graph V) (bin : V → Fin q) (mask : V → Fin 4) : H → Column q :=
  fun e => referenceColumn
    (vertexColumn (coordinatesFromMatching M hM C available bin mask) (actualLeft M H hM C e))
    (vertexColumn (coordinatesFromMatching M hM C available bin mask) (actualRight M H hM C e))

theorem actual_reference_compatible {q} (M H : Graph V) (hM : Matching M) (C : Finset V)
    (available : Graph V) (bin : V → Fin q) (mask : V → Fin 4)
    (hcover : ∀ e∈H, ∃ v∈e.val, v∈C) (e : H) :
    ReferenceCompatible
      (vertexColumn (coordinatesFromMatching M hM C available bin mask) (actualLeft M H hM C e))
      (vertexColumn (coordinatesFromMatching M hM C available bin mask) (actualRight M H hM C e))
      (actualReference M H hM C available bin mask e) := by
  apply referenceColumn_compatible
    _ _ (vertexColumn_is_vertex _ _) (vertexColumn_is_vertex _ _)
  obtain ⟨v,hve,hvC⟩ := hcover e.val e.property
  obtain ⟨i,hi⟩ := orientedEndpoint_surjective C e.val v hve
  fin_cases i
  · left
    rw [actual_center_classification]
    simpa only [actualLeft,Equiv.apply_symm_apply] using (hi.symm ▸ hvC)
  · right
    rw [actual_center_classification]
    simpa only [actualRight,Equiv.apply_symm_apply] using (hi.symm ▸ hvC)

end Actual
end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.actual_endpoint_degree
#print axioms RandomOrderMatching.Analysis.Profile.actual_reference_compatible
