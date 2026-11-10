import RobustMatching.R7ClosedRepairTypedLabeling
import RobustMatching.R7WeightedPhaseAssemblyRelabel

/-! Actual graph specialization of the typed labeling equivalence. Every
typed benchmark edge maps to its own input matching edge, and canonical
center/outside labels are exactly the actual cover partition. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RobustMatching.R7ClosedRepair.TypedLabeling
open RobustMatching.R7SupportFlowMap RobustMatching.R2Cut
open RobustMatching.R7WeightedPhaseAssembly

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
variable (M0 : Graph V) (hM : Matching M0) (C : Finset V) (available : Graph V)
  (bin : V → Fin q) (mask : V → Fin 4)

local notation "D" => coordinatesFromMatching M0 hM C available bin mask

def actualVertexEquiv : CanonicalVertex D ≃ V :=
  (coordinateEquiv D).trans (coveredMatchingCoordinateEquiv M0 hM C)

def actualBenchmarkEquiv : CanonicalBenchmark D ≃ M0 := benchmarkFiberEquiv D

theorem actual_endpoint (b : CanonicalBenchmark D) (t : Bool) :
    actualVertexEquiv M0 hM C available bin mask
      (RobustMatching.R7ClosedRepair.Typed.endpoint
        (P := CenterUnmatched D) (U := OutsideUnmatched D) b t) =
      orientedEndpoint C (actualBenchmarkEquiv M0 hM C available bin mask b).val
        (boolIndex t) := by
  unfold actualVertexEquiv
  rw [Equiv.trans_apply, coordinate_endpoint]
  rfl

lemma oriented_endpoint_pair (e : Edge V) :
    {orientedEndpoint C e 0,orientedEndpoint C e 1} = e.val := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  have himage : Finset.univ.image (orientedEndpoint C e) = e.val := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact endpoint_mem e (coverOrder C e i)
    · intro hv
      obtain ⟨i, hi⟩ := endpoint_surjective e v hv
      refine Finset.mem_image.mpr ⟨(coverOrder C e).symm i, Finset.mem_univ _, ?_⟩
      simpa [orientedEndpoint] using hi
  simpa [hu] using himage

/-- Pointwise preservation of each actual benchmark edge. This is stronger
than matching/rank/cardinality preservation under an unspecified map. -/
theorem actual_benchmark_edge (b : CanonicalBenchmark D) :
    @mapEdge _ _ (Classical.decEq _) (inferInstance : DecidableEq V) (actualVertexEquiv M0 hM C available bin mask)
      (actualVertexEquiv M0 hM C available bin mask).injective
      (RobustMatching.R7ClosedRepair.Typed.benchmarkEdge
        (P := CenterUnmatched D) (U := OutsideUnmatched D) b) =
      (actualBenchmarkEquiv M0 hM C available bin mask b).val := by
  apply Subtype.ext
  simp only [mapEdge, RobustMatching.R7ClosedRepair.Typed.benchmarkEdge,
    Finset.image_insert, Finset.image_singleton, actual_endpoint]
  exact oriented_endpoint_pair C _

/-- Membership in the actual cover is precisely the canonical center
summand, with no assumption that the two partitions coincide. -/
theorem actual_center_iff (v : CanonicalVertex D) :
    actualVertexEquiv M0 hM C available bin mask v ∈ C ↔
      (match v with | .inl _ => True | .inr _ => False) := by
  cases v with
  | inl c =>
      have hh := actual_center_classification M0 hM C available bin mask (coordinateEquiv D (.inl c))
      exact iff_true_intro (hh.mp ((coordinate_is_center D (.inl c)).mpr trivial))
  | inr x =>
      have hh := actual_center_classification M0 hM C available bin mask (coordinateEquiv D (.inr x))
      exact iff_false_intro (fun h => (coordinate_is_center D (.inr x)).mp (hh.mpr h))

theorem actual_center_mem (c : CanonicalCenters D) :
    actualVertexEquiv M0 hM C available bin mask (.inl c) ∈ C :=
  (actual_center_iff M0 hM C available bin mask (.inl c)).mpr trivial

theorem actual_outside_not_mem (x : CanonicalOutsides D) :
    actualVertexEquiv M0 hM C available bin mask (.inr x) ∉ C := by
  intro hx
  exact (actual_center_iff M0 hM C available bin mask (.inr x)).mp hx

def actualCoverEquiv : CanonicalCenters D ≃ {v : V // v ∈ C} :=
  Equiv.ofBijective
    (fun c => ⟨actualVertexEquiv M0 hM C available bin mask (.inl c),
      actual_center_mem M0 hM C available bin mask c⟩) (by
      constructor
      · intro c c' hc
        have he := (actualVertexEquiv M0 hM C available bin mask).injective
          (congrArg Subtype.val hc)
        exact Sum.inl.inj he
      · intro v
        obtain ⟨z,hz⟩ := (actualVertexEquiv M0 hM C available bin mask).surjective v.val
        cases z with
        | inl c => exact ⟨c,Subtype.ext hz⟩
        | inr x =>
            exact False.elim (actual_outside_not_mem M0 hM C available bin mask x
              (hz.symm ▸ v.property)))

def actualOutsideEquiv : CanonicalOutsides D ≃ {v : V // v ∉ C} :=
  Equiv.ofBijective
    (fun x => ⟨actualVertexEquiv M0 hM C available bin mask (.inr x),
      actual_outside_not_mem M0 hM C available bin mask x⟩) (by
      constructor
      · intro x x' hx
        have he := (actualVertexEquiv M0 hM C available bin mask).injective
          (congrArg Subtype.val hx)
        exact Sum.inr.inj he
      · intro v
        obtain ⟨z,hz⟩ := (actualVertexEquiv M0 hM C available bin mask).surjective v.val
        cases z with
        | inl c =>
            exact False.elim (v.property (hz ▸ actual_center_mem M0 hM C available bin mask c))
        | inr x => exact ⟨x,Subtype.ext hz⟩)

theorem actual_center_card : Fintype.card (CanonicalCenters D) = C.card := by
  simpa using Fintype.card_congr (actualCoverEquiv M0 hM C available bin mask)

theorem actual_benchmark_card : Fintype.card (CanonicalBenchmark D) = M0.card := by
  simpa using Fintype.card_congr (actualBenchmarkEquiv M0 hM C available bin mask)

/-- Exact containment for every realized selected benchmark subset. The
state maps may be arbitrarily correlated, including shared parent clocks. -/
theorem actual_selected_subset
    (s : RobustMatching.R7ClosedRepair.Typed.States
      (PairFiber D .gate) (PairFiber D .missing)
      (PairFiber D .internalMissing) (PairFiber D .root)) :
    @mapGraph _ _ (Classical.decEq _) (inferInstance : DecidableEq V) (actualVertexEquiv M0 hM C available bin mask)
      (actualVertexEquiv M0 hM C available bin mask).injective
      (RobustMatching.R7ClosedRepair.Typed.selectedEdges
        (P := CenterUnmatched D) (I := PairFiber D .internalAvailable)
        (U := OutsideUnmatched D) s) ⊆ M0 := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  simp only [RobustMatching.R7ClosedRepair.Typed.selectedEdges, Finset.mem_image] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  rw [actual_benchmark_edge]
  exact (actualBenchmarkEquiv M0 hM C available bin mask b).property

/-- An analytic cut is pulled back from the actual vertices; it is not
identified with the unrelated center/outside partition. -/
theorem actual_side_pullback (side : V → Bool) (v : CanonicalVertex D) :
    side (actualVertexEquiv M0 hM C available bin mask v) =
      Sum.elim
        (fun c => side (actualVertexEquiv M0 hM C available bin mask (.inl c)))
        (fun x => side (actualVertexEquiv M0 hM C available bin mask (.inr x))) v := by
  cases v <;> rfl

end RobustMatching.R7ClosedRepair.TypedLabeling
