import RandomOrderMatching.Analysis.Repair.Labeling.Graph
import RandomOrderMatching.Analysis.Repair.Typed.ReferenceWeights

/-! Ordinary reference incidences under the actual typed vertex bijection.
The adjacency is pulled back from an actual graph, so its edge-containment
interface does not assume a separate embedding of the support graph. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RandomOrderMatching.Analysis.Repair.Labeling
open RandomOrderMatching.Analysis.Profile RandomOrderMatching.Graph
open RandomOrderMatching.Phases.Execution RandomOrderMatching.Graph.BipartiteMatrix

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
variable (M0 : Graph V) (hM : Matching M0) (C : Finset V) (available : Graph V)
  (bin : V → Fin q) (mask : V → Fin 4)

local notation "D" => coordinatesFromMatching M0 hM C available bin mask

def actualReferenceEdge (c : CanonicalCenters D) (x : CanonicalOutsides D) : Edge V :=
  @mapEdge _ _ (Classical.decEq _) (inferInstance : DecidableEq V)
    (actualVertexEquiv M0 hM C available bin mask)
    (actualVertexEquiv M0 hM C available bin mask).injective (edgeOf (c,x))

def actualReferenceAdj (H : Graph V) : CanonicalCenters D → CanonicalOutsides D → Prop :=
  fun c x => actualReferenceEdge M0 hM C available bin mask c x ∈ H

theorem actual_reference_endpoints (c : CanonicalCenters D) (x : CanonicalOutsides D) :
    (actualReferenceEdge M0 hM C available bin mask c x).val =
      {actualVertexEquiv M0 hM C available bin mask (.inl c),
       actualVertexEquiv M0 hM C available bin mask (.inr x)} := by
  simp [actualReferenceEdge, mapEdge, edgeOf]

/-- Every ordinary support edge is an actual reference edge between the
specified actual center and actual outside vertex. -/
theorem actual_reference_graph_subset (H : Graph V) :
    @mapGraph _ _ (Classical.decEq _) (inferInstance : DecidableEq V)
      (actualVertexEquiv M0 hM C available bin mask)
      (actualVertexEquiv M0 hM C available bin mask).injective
      (graphEdges (actualReferenceAdj M0 hM C available bin mask H)) ⊆ H := by
  intro e he
  simp only [mapGraph, Finset.mem_image] at he
  obtain ⟨a, ha, rfl⟩ := he
  simp only [graphEdges, Finset.mem_image] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  exact (Finset.mem_filter.mp hp).2

/-- The normalized degree labels and affine-arm masks are evaluated at
the same actual vertex as the support and benchmark edges. -/
theorem actual_bin_pullback (v : CanonicalVertex D) :
    (D).bin (coordinateEquiv D v) = bin (actualVertexEquiv M0 hM C available bin mask v) := rfl

theorem actual_mask_pullback (v : CanonicalVertex D) :
    (D).mask (coordinateEquiv D v) = mask (actualVertexEquiv M0 hM C available bin mask v) := rfl

/-- Capped repair weights are exactly the actual edge indicator times the
outside-vertex degree denominator, after the proven vertex relabeling. -/
theorem actual_reference_weight (H : Graph V) (β δ : ℝ) (a : V → ℝ)
    (c : CanonicalCenters D) (x : CanonicalOutsides D) :
    RandomOrderMatching.Analysis.Repair.Typed.referenceWeight
      (fun x c => actualReferenceAdj M0 hM C available bin mask H c x) β δ
      (fun x => a (actualVertexEquiv M0 hM C available bin mask (.inr x))) c x =
      if actualReferenceEdge M0 hM C available bin mask c x ∈ H then
        1 / (β * max δ (1-a (actualVertexEquiv M0 hM C available bin mask (.inr x))))
      else 0 := by
  unfold RandomOrderMatching.Analysis.Repair.Typed.referenceWeight
    RandomOrderMatching.Analysis.Support.cappedWeight actualReferenceAdj
  exact (ite_eq_ite _ _ _).mpr trivial

end RandomOrderMatching.Analysis.Repair.Labeling
