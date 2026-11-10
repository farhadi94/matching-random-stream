import RobustMatching.R7SupportFlowMapActualMasks

noncomputable section
open scoped BigOperators
open Classical
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R2Cut RobustMatching.R7ReductionCertificate
open RobustMatching.R7ClosedRepair.TypedLabeling

section Actual
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (M : Graph V) (hM : Matching M) (C : Finset V) (available : Graph V)
  (bin : V → Fin 152)

theorem actual_vertex_mask_independent (m1 m2 : V → Fin 4)
    (v : CanonicalVertex (coordinatesFromMatching M hM C available bin m1)) :
    actualVertexEquiv M hM C available bin m1 v=actualVertexEquiv M hM C available bin m2 v := by
  rcases v with c | x
  · rcases c with g | m | p | i | j <;> rfl
  · rcases x with r | m | g | u <;> rfl

theorem actual_adj_mask_independent (m1 m2 : V → Fin 4) (H : Graph V)
    (c : CanonicalCenters (coordinatesFromMatching M hM C available bin m1))
    (x : CanonicalOutsides (coordinatesFromMatching M hM C available bin m1)) :
    actualReferenceAdj M hM C available bin m1 H c x ↔
      actualReferenceAdj M hM C available bin m2 H c x := by
  have he : actualReferenceEdge M hM C available bin m1 c x =
      actualReferenceEdge M hM C available bin m2 c x := by
    apply Subtype.ext
    erw [actual_reference_endpoints,actual_reference_endpoints,
      actual_vertex_mask_independent M hM C available bin m1 m2 (.inl c),
      actual_vertex_mask_independent M hM C available bin m1 m2 (.inr x)]
    rfl
  change _∈H ↔ _∈H
  rw [he]

theorem actual_binWeight_explicit (mask : V → Fin 4) (H : Graph V) (beta : ℝ)
    (c : CanonicalCenters (coordinatesFromMatching M hM C available bin mask))
    (x : CanonicalOutsides (coordinatesFromMatching M hM C available bin mask)) :
    binWeight (coordinatesFromMatching M hM C available bin mask) Concrete.data beta
      (actualReferenceAdj M hM C available bin mask H) c x =
      if actualReferenceAdj M hM C available bin mask H c x then
        1/(beta*(max Concrete.data.cap
          (1-lower Concrete.data (bin (actualVertexEquiv M hM C available bin mask (.inr x)))) : ℚ)) else 0 := rfl

theorem actual_binWeight_mask_independent (m1 m2 : V → Fin 4) (H : Graph V) (beta : ℝ)
    (c : CanonicalCenters (coordinatesFromMatching M hM C available bin m1))
    (x : CanonicalOutsides (coordinatesFromMatching M hM C available bin m1)) :
    binWeight (coordinatesFromMatching M hM C available bin m1) Concrete.data beta
      (actualReferenceAdj M hM C available bin m1 H) c x =
    binWeight (coordinatesFromMatching M hM C available bin m2) Concrete.data beta
      (actualReferenceAdj M hM C available bin m2 H) c x := by
  erw [actual_binWeight_explicit,actual_binWeight_explicit,
    actual_vertex_mask_independent M hM C available bin m1 m2 (.inr x)]
  by_cases h1 : actualReferenceAdj M hM C available bin m1 H c x
  · have h2 := (actual_adj_mask_independent M hM C available bin m1 m2 H c x).mp h1
    simp only [if_pos h1,if_pos h2]
    rfl
  · have h2 : ¬actualReferenceAdj M hM C available bin m2 H c x :=
      fun h2 => h1 ((actual_adj_mask_independent M hM C available bin m1 m2 H c x).mpr h2)
    simp only [if_neg h1,if_neg h2]

def actualMinimumMask (H : Graph V) (beta : ℝ) (v : V) : Fin 4 :=
  let d := coordinatesFromMatching M hM C available bin (fun _ => 0)
  let w := binWeight d Concrete.data beta (actualReferenceAdj M hM C available bin (fun _ => 0) H)
  match (actualVertexEquiv M hM C available bin (fun _ => 0)).symm v with
  | .inl _ => 0
  | .inr x => loadMask Concrete.data (outsideType d x)
      (RobustMatching.R7ClosedRepair.Typed.primaryLoad (Concrete.data.alpha : ℝ) w x)
      (RobustMatching.R7ClosedRepair.Typed.secondaryLoad (Concrete.data.omega : ℝ) w x)

theorem actualMinimumMask_identity (H : Graph V) (beta : ℝ)
    (x : CanonicalOutsides (coordinatesFromMatching M hM C available bin
      (actualMinimumMask M hM C available bin H beta))) :
    let mask := actualMinimumMask M hM C available bin H beta
    let d := coordinatesFromMatching M hM C available bin mask
    d.mask (coordinateEquiv d (.inr x)) = loadMask Concrete.data (outsideType d x)
      (RobustMatching.R7ClosedRepair.Typed.primaryLoad (Concrete.data.alpha : ℝ)
        (binWeight d Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x)
      (RobustMatching.R7ClosedRepair.Typed.secondaryLoad (Concrete.data.omega : ℝ)
        (binWeight d Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x) := by
  let mask := actualMinimumMask M hM C available bin H beta
  let d := coordinatesFromMatching M hM C available bin mask
  let d0 := coordinatesFromMatching M hM C available bin (fun _ => 0)
  have hp : RobustMatching.R7ClosedRepair.Typed.primaryLoad (Concrete.data.alpha : ℝ)
      (binWeight d Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x =
      RobustMatching.R7ClosedRepair.Typed.primaryLoad (Concrete.data.alpha : ℝ)
      (binWeight d0 Concrete.data beta (actualReferenceAdj M hM C available bin (fun _ => 0) H)) x := by
    apply Finset.sum_congr rfl
    intro c _
    rw [actual_binWeight_mask_independent M hM C available bin mask (fun _ => 0) H beta c x]
    rfl
  have hs : RobustMatching.R7ClosedRepair.Typed.secondaryLoad (Concrete.data.omega : ℝ)
      (binWeight d Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x =
      RobustMatching.R7ClosedRepair.Typed.secondaryLoad (Concrete.data.omega : ℝ)
      (binWeight d0 Concrete.data beta (actualReferenceAdj M hM C available bin (fun _ => 0) H)) x := by
    apply Finset.sum_congr rfl
    intro c _
    rw [actual_binWeight_mask_independent M hM C available bin mask (fun _ => 0) H beta c x]
    rfl
  have ht : outsideType d x=outsideType d0 x := by rcases x with r | m | g | u <;> rfl
  change mask (actualVertexEquiv M hM C available bin mask (.inr x)) = _
  rw [actual_vertex_mask_independent M hM C available bin mask (fun _ => 0) (.inr x)]
  change actualMinimumMask M hM C available bin H beta
    (actualVertexEquiv M hM C available bin (fun _ => 0) (.inr x)) = _
  simp only [actualMinimumMask,Equiv.symm_apply_apply]
  rw [hp,hs,ht]

end Actual
end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.actualMinimumMask_identity
