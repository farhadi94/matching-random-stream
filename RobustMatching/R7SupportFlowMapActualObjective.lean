import RobustMatching.R7SupportFlowMapTypedProfile
import RobustMatching.R7SupportFlowMapActualReference
import RobustMatching.R7ClosedRepairTypedLabelingReferenceSum

noncomputable section
open scoped BigOperators
open Classical
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R2Cut RobustMatching.R7ReductionCertificate
open RobustMatching.R7ClosedRepair.TypedLabeling

section Actual
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
variable (M : Graph V) (hM : Matching M) (C : Finset V) (available : Graph V)
  (bin : V → Fin q) (mask : V → Fin 4)
local notation "D" => coordinatesFromMatching M hM C available bin mask

def edgeReferenceTag (e : Edge V) : Column q :=
  referenceColumn
    (vertexColumn D ((coveredMatchingCoordinateEquiv M hM C).symm (orientedEndpoint C e 0)))
    (vertexColumn D ((coveredMatchingCoordinateEquiv M hM C).symm (orientedEndpoint C e 1)))

theorem edgeReferenceTag_pair (c : CanonicalCenters D) (x : CanonicalOutsides D) :
    edgeReferenceTag M hM C available bin mask (actualReferenceEdge M hM C available bin mask c x) =
      .cross (canonicalCenterClass D c) (canonicalOutsideClass D x) := by
  obtain ⟨h0,h1⟩ := actual_reference_oriented_endpoints M hM C available bin mask c x
  unfold edgeReferenceTag
  rw [h0,h1]
  simp only [actualVertexEquiv,Equiv.trans_apply,Equiv.symm_apply_apply,
    coordinate_vertex_column,canonicalColumn,referenceColumn,canonicalCenterClass,canonicalOutsideClass]

theorem edgeReferenceTag_phase_zero (data : ProfileData q) (e : Edge V)
    (hne : (e.val ∩ C).card ≠ 1) :
    coeffLe data .phase (edgeReferenceTag M hM C available bin mask e)=0 := by
  let v0 := (coveredMatchingCoordinateEquiv M hM C).symm (orientedEndpoint C e 0)
  let v1 := (coveredMatchingCoordinateEquiv M hM C).symm (orientedEndpoint C e 1)
  have hv0 := vertexColumn_is_vertex D v0
  have hv1 := vertexColumn_is_vertex D v1
  have hc0 : IsCenterColumn (vertexColumn D v0) ↔ orientedEndpoint C e 0∈C := by
    simpa only [v0,Equiv.apply_symm_apply] using
      actual_center_classification M hM C available bin mask v0
  have hc1 : IsCenterColumn (vertexColumn D v1) ↔ orientedEndpoint C e 1∈C := by
    simpa only [v1,Equiv.apply_symm_apply] using
      actual_center_classification M hM C available bin mask v1
  have hcross (h0 : orientedEndpoint C e 0∈C) (h1 : orientedEndpoint C e 1∉C) : False := by
    apply hne
    rw [←oriented_endpoint_pair C e]
    have he : ({orientedEndpoint C e 0,orientedEndpoint C e 1} ∩ C) =
        ({orientedEndpoint C e 0} : Finset V) := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨hv | hv,hC⟩
        · exact hv
        · exact False.elim (h1 (hv ▸ hC))
      · intro hv; exact ⟨Or.inl hv,hv.symm ▸ h0⟩
    rw [he]
    simp
  change coeffLe data .phase (referenceColumn (vertexColumn D v0) (vertexColumn D v1))=0
  cases h0 : vertexColumn D v0 <;> cases h1 : vertexColumn D v1 <;>
    simp [h0,h1,IsVertexColumn,IsCenterColumn] at hv0 hv1 hc0 hc1
  · dsimp only [referenceColumn]
    split_ifs <;> simp [coeffLe,leTerms,coeff]
  · exact False.elim (hcross hc0 hc1)
  · exact False.elim (hc0 (oriented_center_first C e hc1))
  · simp [referenceColumn,coeffLe,leTerms,coeff]

theorem actual_reference_phase_sum (H : Graph V) (data : ProfileData q) :
    (∑ e : H, (coeffLe data .phase (actualReference M H hM C available bin mask e) : ℝ)) =
      ∑ c : CanonicalCenters D, ∑ x : CanonicalOutsides D,
        if actualReferenceAdj M hM C available bin mask H c x then
          (edgeCredit data (canonicalCenterClass D c) (canonicalOutsideClass D x) : ℝ) else 0 := by
  classical
  let f : Edge V → ℝ := fun e => coeffLe data .phase (edgeReferenceTag M hM C available bin mask e)
  have hfilter : (∑ e∈H, f e) = ∑ e∈actualCrossEdges C H, f e := by
    rw [actualCrossEdges,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : (e.val∩C).card=1
    · simp [he]
    · simp [he,f,edgeReferenceTag_phase_zero M hM C available bin mask data e he]
  calc
    _ = ∑ e∈H, f e := by
      rw [←Finset.sum_coe_sort H]
      rfl
    _ = ∑ e∈actualCrossEdges C H, f e := hfilter
    _ = ∑ e : actualCrossEdges C H, f e.val := by rw [Finset.sum_coe_sort]
    _ = ∑ e : actualCrossEdges C H,
        (edgeCredit data
          (canonicalCenterClass D ((actualReferencePairEquiv M hM C available bin mask H).symm e).val.1)
          (canonicalOutsideClass D ((actualReferencePairEquiv M hM C available bin mask H).symm e).val.2) : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      let p := (actualReferencePairEquiv M hM C available bin mask H).symm e
      have hp : actualReferenceEdge M hM C available bin mask p.val.1 p.val.2=e.val := by
        exact congrArg Subtype.val ((actualReferencePairEquiv M hM C available bin mask H).apply_symm_apply e)
      dsimp only [f]
      rw [←hp,edgeReferenceTag_pair]
      simp [coeffLe,leTerms,coeff,p]
    _ = _ := actual_reference_sum M hM C available bin mask H
      (fun c x => (edgeCredit data (canonicalCenterClass D c) (canonicalOutsideClass D x) : ℝ))

end Actual
end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.actual_reference_phase_sum
