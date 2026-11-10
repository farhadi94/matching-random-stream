import RobustMatching.R7GraphComponents
import RobustMatching.R6FableImportancePhase
import RobustMatching.R6FableAlgebraSubmodular
import Mathlib.Topology.Order.Lattice

/-!
Actual finite marked matching-pair value and its elementary graph properties.
The weighted Tutte-minor representation is NOT postulated here.
-/
noncomputable section
open scoped BigOperators symmDiff

namespace RobustMatching.R7AlgebraPath
open RobustMatching.R2Cut RobustMatching.Lower RobustMatching.R7GraphKonig

variable {V : Type*} [Fintype V] [DecidableEq V]

def Separated (G : Graph V) (marks : Finset V) : Prop :=
  ∀ u ∈ marks, ∀ v ∈ marks, (simpleGraph G).Reachable u v → u = v

def Admissible (N₁ N₂ : Graph V) (marks : Finset V) : Prop :=
  Matching N₁ ∧ Matching N₂ ∧ Disjoint (covered N₁) marks ∧
    Separated (N₁ ∆ N₂) marks

theorem simpleGraph_empty : simpleGraph (∅ : Graph V) = ⊥ := by
  ext u v
  simp [simpleGraph, SimpleGraph.fromEdgeSet]

theorem empty_admissible (marks : Finset V) :
    Admissible (∅ : Graph V) ∅ marks := by
  refine ⟨RobustMatching.R6FableImportance.empty_matching,
    RobustMatching.R6FableImportance.empty_matching, ?_, ?_⟩
  · simp [covered]
  · intro u hu v hv hr
    change (simpleGraph (∅ : Graph V)).Reachable u v at hr
    rw [simpleGraph_empty, SimpleGraph.reachable_bot] at hr
    exact hr

theorem same_admissible_empty (N : Graph V) (hN : Matching N) : Admissible N N ∅ := by
  refine ⟨hN, hN, by simp, ?_⟩
  intro u hu
  simp at hu

theorem admissible_mono_marks {N₁ N₂ : Graph V} {A B : Finset V}
    (h : Admissible N₁ N₂ B) (hAB : A ⊆ B) : Admissible N₁ N₂ A := by
  refine ⟨h.1, h.2.1, h.2.2.1.mono_right hAB, ?_⟩
  intro u hu v hv hr
  exact h.2.2.2 u (hAB hu) v (hAB hv) hr

def feasiblePairs (G : Graph V) (marks : Finset V) : Finset (Graph V × Graph V) := by
  classical
  exact (G.powerset ×ˢ G.powerset).filter (fun p => Admissible p.1 p.2 marks)

theorem mem_feasiblePairs (G : Graph V) (marks : Finset V) (p : Graph V × Graph V) :
    p ∈ feasiblePairs G marks ↔ p.1 ⊆ G ∧ p.2 ⊆ G ∧ Admissible p.1 p.2 marks := by
  classical
  simp [feasiblePairs, and_assoc]

theorem feasiblePairs_nonempty (G : Graph V) (marks : Finset V) :
    (feasiblePairs G marks).Nonempty := by
  refine ⟨(∅,∅), (mem_feasiblePairs G marks (∅,∅)).mpr ?_⟩
  exact ⟨Finset.empty_subset _, Finset.empty_subset _, empty_admissible marks⟩

def pairWeight (w : Edge V → ℝ) (p : Graph V × Graph V) : ℝ :=
  (∑ e ∈ p.1, w e) + ∑ e ∈ p.2, w e

def pathValue (w : Edge V → ℝ) (G : Graph V) (marks : Finset V) : ℝ :=
  (feasiblePairs G marks).sup' (feasiblePairs_nonempty G marks) (pairWeight w)

theorem pathValue_attained (w : Edge V → ℝ) (G : Graph V) (marks : Finset V) :
    ∃ p ∈ feasiblePairs G marks, pathValue w G marks = pairWeight w p := by
  exact Finset.exists_mem_eq_sup' (feasiblePairs_nonempty G marks) (pairWeight w)

theorem pairWeight_le_pathValue (w : Edge V → ℝ) {G N₁ N₂ : Graph V}
    {marks : Finset V} (hN₁ : N₁ ⊆ G) (hN₂ : N₂ ⊆ G)
    (h : Admissible N₁ N₂ marks) :
    pairWeight w (N₁,N₂) ≤ pathValue w G marks := by
  exact Finset.le_sup' (pairWeight w)
    ((mem_feasiblePairs G marks (N₁,N₂)).mpr ⟨hN₁,hN₂,h⟩)

def deleteVertices (G : Graph V) (marks : Finset V) : Graph V := by
  classical
  exact G.filter (fun e => Disjoint e.val marks)

theorem avoiding_subset_delete {G N : Graph V} {marks : Finset V}
    (hN : N ⊆ G) (ha : Disjoint (covered N) marks) : N ⊆ deleteVertices G marks := by
  intro e he
  apply Finset.mem_filter.mpr
  refine ⟨hN he, ?_⟩
  exact ha.mono_left (fun v hv => mem_covered.mpr ⟨e,he,hv⟩)

theorem pathValue_one_set_upper (w : Edge V → ℝ) (G : Graph V) (marks : Finset V) :
    pathValue w G marks ≤ RobustMatching.R6FableImportance.opt w G +
      RobustMatching.R6FableImportance.opt w (deleteVertices G marks) := by
  obtain ⟨p, hp, hv⟩ := pathValue_attained w G marks
  obtain ⟨h₁, h₂, hadm⟩ := (mem_feasiblePairs G marks p).mp hp
  have ha := weight_le_packingOpt Matching RobustMatching.R6FableImportance.empty_matching w
    hadm.1 (avoiding_subset_delete h₁ hadm.2.2.1)
  have hb := weight_le_packingOpt Matching RobustMatching.R6FableImportance.empty_matching w
    hadm.2.1 h₂
  rw [hv]
  unfold pairWeight RobustMatching.R6FableImportance.opt
  linarith

theorem pathValue_empty (w : Edge V → ℝ) (G : Graph V) :
    pathValue w G ∅ = 2 * RobustMatching.R6FableImportance.opt w G := by
  apply le_antisymm
  · have hh := pathValue_one_set_upper w G ∅
    have he : deleteVertices G ∅ = G := by ext e; simp [deleteVertices]
    rw [he] at hh
    linarith
  · obtain ⟨N, hNG, hN, hv⟩ := packingOpt_attained Matching
      RobustMatching.R6FableImportance.empty_matching w G
    have hh := pairWeight_le_pathValue w hNG hNG (same_admissible_empty N hN)
    unfold pairWeight at hh
    change RobustMatching.R6FableImportance.opt w G = ∑ e ∈ N, w e at hv
    linarith

theorem pathValue_antitone_marks (w : Edge V → ℝ) (G : Graph V)
    {A B : Finset V} (hAB : A ⊆ B) : pathValue w G B ≤ pathValue w G A := by
  obtain ⟨p, hp, hv⟩ := pathValue_attained w G B
  obtain ⟨h₁,h₂,hadm⟩ := (mem_feasiblePairs G B p).mp hp
  rw [hv]
  exact pairWeight_le_pathValue w h₁ h₂ (admissible_mono_marks hadm hAB)

theorem continuous_pairWeight (p : Graph V × Graph V) :
    Continuous (fun w : Edge V → ℝ => pairWeight w p) := by
  unfold pairWeight
  fun_prop

/-- The actual graph value is continuous in every original edge weight.
This supplies the real-weight extension once the integer-weight bridge is proved. -/
theorem continuous_pathValue (G : Graph V) (marks : Finset V) :
    Continuous (fun w : Edge V → ℝ => pathValue w G marks) := by
  exact Continuous.finset_sup'_apply (feasiblePairs_nonempty G marks)
    (fun p _ => continuous_pairWeight p)

theorem weight_difference_bound (w v : Edge V → ℝ) {G N : Graph V} (hN : N ⊆ G) :
    |(∑ e ∈ N, w e) - ∑ e ∈ N, v e| ≤ ∑ e ∈ G, |w e-v e| := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ e ∈ N, (w e-v e)| ≤ ∑ e ∈ N, |w e-v e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ G, |w e-v e| :=
      Finset.sum_le_sum_of_subset_of_nonneg hN (fun e _ _ => abs_nonneg _)

theorem pairWeight_difference_bound (w v : Edge V → ℝ) {G : Graph V}
    {p : Graph V × Graph V} (h₁ : p.1 ⊆ G) (h₂ : p.2 ⊆ G) :
    |pairWeight w p - pairWeight v p| ≤ 2 * ∑ e ∈ G, |w e-v e| := by
  have h₁' := weight_difference_bound w v h₁
  have h₂' := weight_difference_bound w v h₂
  unfold pairWeight
  calc
    |((∑ e ∈ p.1, w e) + ∑ e ∈ p.2, w e) -
      ((∑ e ∈ p.1, v e) + ∑ e ∈ p.2, v e)| =
      |((∑ e ∈ p.1, w e) - ∑ e ∈ p.1, v e) +
        ((∑ e ∈ p.2, w e) - ∑ e ∈ p.2, v e)| := by congr 1 <;> ring
    _ ≤ |(∑ e ∈ p.1, w e) - ∑ e ∈ p.1, v e| +
        |(∑ e ∈ p.2, w e) - ∑ e ∈ p.2, v e| := abs_add_le _ _
    _ ≤ 2 * ∑ e ∈ G, |w e-v e| := by linarith

theorem pathValue_sub_le (w v : Edge V → ℝ) (G : Graph V) (marks : Finset V) :
    pathValue w G marks - pathValue v G marks ≤ 2 * ∑ e ∈ G, |w e-v e| := by
  obtain ⟨p,hp,hv⟩ := pathValue_attained w G marks
  obtain ⟨h₁,h₂,hadm⟩ := (mem_feasiblePairs G marks p).mp hp
  have hu := pairWeight_le_pathValue v h₁ h₂ hadm
  have hd := (abs_le.mp (pairWeight_difference_bound w v h₁ h₂)).2
  linarith

/-- A quantitative range-free stability bound for the graph-defined value. -/
theorem pathValue_lipschitz_l1 (w v : Edge V → ℝ) (G : Graph V) (marks : Finset V) :
    |pathValue w G marks - pathValue v G marks| ≤ 2 * ∑ e ∈ G, |w e-v e| := by
  apply abs_le.mpr
  constructor
  · have hh := pathValue_sub_le v w G marks
    simp_rw [abs_sub_comm (v _) (w _)] at hh
    linarith
  · exact pathValue_sub_le w v G marks

end RobustMatching.R7AlgebraPath
