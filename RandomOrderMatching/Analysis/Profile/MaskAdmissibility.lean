import RandomOrderMatching.Analysis.Profile.GraphWeights
import RandomOrderMatching.Analysis.Profile.MaskBounds
import RandomOrderMatching.Analysis.Profile.DegreeBins

noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Graph RandomOrderMatching.Certificates.DegreeProfile
open RandomOrderMatching.Analysis.Repair.Labeling

section Actual
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (M : Graph V) (hM : Matching M) (C : Finset V) (available : Graph V)
  (bin : V → Fin 152) (mask : V → Fin 4)
local notation "D" => coordinatesFromMatching M hM C available bin mask

theorem actual_low_bin_loads (H : Graph V) (beta : ℝ) (hbeta : 0 < beta)
    (hbin : ∀ v, incidenceDegree H v ≤ beta*(upper Concrete.data (bin v) : ℝ))
    (x : CanonicalOutsides D) (hlow : upper Concrete.data (canonicalOutsideClass D x).1 ≤ 1/2) :
    RandomOrderMatching.Analysis.Repair.Typed.primaryLoad (Concrete.data.alpha : ℝ)
      (binWeight D Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x ≤ 1 ∧
    RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad (Concrete.data.omega : ℝ)
      (binWeight D Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x ≤ 1 := by
  apply bin_loads_low D Concrete.data beta _ hbeta
    (by norm_num [Concrete.data]) (by norm_num [Concrete.data]) (by norm_num [Concrete.data])
  apply binWeight_low_column D Concrete.data beta _ hbeta (by norm_num [Concrete.data]) x
  · exact (actual_reference_column_count M hM C available bin mask H x).trans
      (hbin (actualVertexEquiv M hM C available bin mask (.inr x)))
  · exact (Concrete.data_grid_strict (canonicalOutsideClass D x).1).le
  · exact hlow

theorem actual_mask_admissibility (H : Graph V) (beta : ℝ) (hbeta : 0 < beta)
    (hbin : ∀ v, incidenceDegree H v ≤ beta*(upper Concrete.data (bin v) : ℝ))
    (hmask : ∀ x : CanonicalOutsides D, (D).mask (coordinateEquiv D (.inr x)) =
      loadMask Concrete.data (outsideType D x)
        (RandomOrderMatching.Analysis.Repair.Typed.primaryLoad (Concrete.data.alpha : ℝ)
          (binWeight D Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x)
        (RandomOrderMatching.Analysis.Repair.Typed.secondaryLoad (Concrete.data.omega : ℝ)
          (binWeight D Concrete.data beta (actualReferenceAdj M hM C available bin mask H)) x))
    (v : MatchingVertex M) : columnAllowed Concrete.data (vertexColumn D v) := by
  obtain ⟨z,rfl⟩ := (coordinateEquiv D).surjective v
  rw [coordinate_vertex_column]
  cases z with
  | inl c => trivial
  | inr x =>
    change outsideAllowed Concrete.data (_,outsideType D x,(D).mask (coordinateEquiv D (.inr x)))
    rw [hmask]
    apply loadMask_allowed
    intro _ hh
    exact actual_low_bin_loads M hM C available bin mask H beta hbeta hbin x hh

end Actual
end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.actual_mask_admissibility
