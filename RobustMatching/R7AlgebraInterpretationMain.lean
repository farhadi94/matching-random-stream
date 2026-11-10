import RobustMatching.R7AlgebraInterpretationEnvelope
import RobustMatching.R7ProbabilityOrbitColor
import RobustMatching.R7WeightedPhaseAlgebraLowerFactor

/-!
Actual comparison with the graph-defined marked matching-pair optimum.
The upper direction composes global cancellation, finite column indexing,
orbit parity coloring, and the actual graph factor realization.
-/
noncomputable section
open scoped BigOperators
open Equiv Finset

namespace RobustMatching.R7AlgebraInterpretation
open RobustMatching.R7Algebra RobustMatching.R7AlgebraTutte
open RobustMatching.R7GraphInterpretation RobustMatching.R7GraphKonig
open RobustMatching.R7AlgebraPath RobustMatching.R2Cut
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Every actual maximal Tutte-minor degree is bounded by an actual admissible
matching pair in the original graph. No representation premise remains here. -/
theorem markedTutteValue_le_pathValue (G : Graph V) (w : Sym2 V → ℕ)
    (marks : Finset V) :
    (markedTutteValue (simpleGraph G) w marks : ℝ) ≤
      pathValue (originalWeight w) G marks := by
  obtain ⟨I,π,hG,havail,hcycles,hdeg⟩ :=
    availableTutte_upper_witness (simpleGraph G) w (Finset.univ \ marks)
  let F := partialArcs I π
  have hloop : ∀ i ∈ I, π i ≠ i := by
    intro i hi
    exact (simpleGraph G).ne_of_adj (hG i hi) |>.symm
  have hf : EvenFactor F := by
    refine ⟨partialArcs_matching I π,?_,?_⟩
    · intro p hp
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
      exact (hloop i hi).symm
    · exact partial_permutation_colorable I π hloop hcycles
  have hFG : ∀ p ∈ F, (simpleGraph G).Adj p.1 p.2 := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact hG i hi
  have ha : Disjoint (targetSupport F) marks := by
    apply Finset.disjoint_left.mpr
    intro v hv hm
    rw [show targetSupport F = I.image π from partialArcs_target I π] at hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_sdiff.mp (havail i hi)).2 hm
  have hg := evenFactor_weight_le_pathValue (originalWeight w) G F marks hf hFG ha
  rw [factor_weight_originalWeight w F hf.loopless] at hg
  change ((∑ p ∈ partialArcs I π, w s(p.1,p.2) : ℕ) : ℝ) ≤ _ at hg
  rw [partialArcs_weight_sum] at hg
  have hd : (markedTutteValue (simpleGraph G) w marks : ℝ) ≤
      ((∑ i ∈ I, w s(i,π i) : ℕ) : ℝ) := by
    change (availableTutteValue (simpleGraph G) w (Finset.univ \ marks) : ℝ) ≤ _
    exact_mod_cast hdeg
  exact hd.trans hg

/-- Every actual admissible matching pair supplies an actual nonzero Tutte
minor of at least its weight, with exactly the allowed target columns. -/
theorem pathValue_le_markedTutteValue (G : Graph V) (w : Sym2 V → ℕ)
    (marks : Finset V) :
    pathValue (originalWeight w) G marks ≤
      (markedTutteValue (simpleGraph G) w marks : ℝ) := by
  classical
  obtain ⟨F,hf,ha,hFG,hval⟩ := pathValue_attained_by_evenFactor (originalWeight w) G marks
  obtain ⟨π,hπ⟩ := matching_arcs_completion F hf.matching
  let I := sourceSupport F
  have hG : ∀ i ∈ I, (simpleGraph G).Adj i (π i) := by
    intro i hi
    apply hFG (i,π i)
    rw [←hπ]
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  have hcolor : (arcSupport (I.image (fun i => (i,π i)))).Colorable 2 := by
    change (arcSupport (partialArcs I π)).Colorable 2
    rw [hπ]
    exact hf.colorable
  obtain ⟨hn,hd⟩ := RobustMatching.R7WeightedPhaseAlgebraLower.tutte_partial_factor_lower
    (simpleGraph G) w I π hG hcolor
  have hc := (completed_principal_minor_nonzero I (weightedTutte (simpleGraph G) w) π).mpr hn
  have hcols : ∀ i ∈ I, π i ∈ Finset.univ \ marks := by
    intro i hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hm
    apply Finset.disjoint_left.mp ha _ hm
    apply Finset.mem_image.mpr
    refine ⟨(i,π i),?_,rfl⟩
    rw [←hπ]
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  have he := completed_minor_le_available (simpleGraph G) w (Finset.univ \ marks) I π hc hcols
  rw [completed_principal_minor_degree] at he
  have hsum : (∑ i : {v // v ∈ I}, (w s(i.val,π i.val) : ℤ)) =
      ∑ i ∈ I, (w s(i,π i) : ℤ) := Finset.sum_coe_sort I (fun i => (w s(i,π i) : ℤ))
  have hl : (∑ i ∈ I, (w s(i,π i) : ℤ)) ≤ markedTutteValue (simpleGraph G) w marks := by
    rw [hsum] at hd
    exact hd.trans he
  rw [hval,factor_weight_originalWeight w F hf.loopless,←hπ,partialArcs_weight_sum]
  exact_mod_cast hl

/-- Full actual generic weighted Tutte interpretation for finite integer
weights. Both matrix and graph optima are independently defined. -/
theorem markedTutteValue_eq_pathValue (G : Graph V) (w : Sym2 V → ℕ)
    (marks : Finset V) :
    (markedTutteValue (simpleGraph G) w marks : ℝ) =
      pathValue (originalWeight w) G marks :=
  le_antisymm (markedTutteValue_le_pathValue G w marks)
    (pathValue_le_markedTutteValue G w marks)

/-- The graph-defined marked matching-pair optimum is submodular for actual
integer weights, with no representation or exchange premise. -/
theorem pathValue_submodular_nat (G : Graph V) (w : Sym2 V → ℕ) :
    RobustMatching.R6FableAlgebraSubmodular.Submodular (pathValue (originalWeight w) G) := by
  intro S T
  have hh := markedTutteValue_submodular (simpleGraph G) w S T
  have hh' : (markedTutteValue (simpleGraph G) w (S ∪ T) : ℝ) +
      (markedTutteValue (simpleGraph G) w (S ∩ T) : ℝ) ≤
      (markedTutteValue (simpleGraph G) w S : ℝ) +
      (markedTutteValue (simpleGraph G) w T : ℝ) := by exact_mod_cast hh
  simpa only [markedTutteValue_eq_pathValue] using hh'

end RobustMatching.R7AlgebraInterpretation
