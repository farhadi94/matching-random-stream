import RobustMatching.R7GraphKonig
import Mathlib.Data.Real.Basic

/-! Actual nonnegative edge flows with vertex loads at most one round to
an integral matching in every finite bipartite project graph. The matching
and equal-size cover are constructed via Hall; they are not hypotheses. -/

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RobustMatching.R7GraphKonig
open RobustMatching.R2Cut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A Boolean cut that separates every edge is an actual bipartite coloring. -/
theorem colorable_of_cut (G : Graph V) (cut : V → Bool)
    (hcut : ∀ e ∈ G, ∀ u ∈ e.val, ∀ v ∈ e.val, u ≠ v → cut u ≠ cut v) :
    (simpleGraph G).Colorable 2 := by
  let c : V → Fin 2 := fun v => if cut v then 1 else 0
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro u v huv
  obtain ⟨⟨e, he, heq⟩, hne⟩ := huv
  have hu : u ∈ e.val := by rw [← heq]; simp
  have hv : v ∈ e.val := by rw [← heq]; simp
  have hh := hcut e he u hu v hv hne
  cases hcu : cut u <;> cases hcv : cut v <;> simp_all [c]

/-- Weak fractional duality for the actual finite edge-incidence sums. -/
theorem fractional_le_cover (G : Graph V) (w : Edge V → ℝ) (C : Finset V)
    (hw : ∀ e ∈ G, 0 ≤ w e)
    (hload : ∀ v, (∑ e ∈ G, if v ∈ e.val then w e else 0) ≤ 1)
    (hC : ∀ e ∈ G, (e.val ∩ C).Nonempty) :
    (∑ e ∈ G, w e) ≤ (C.card : ℝ) := by
  calc
    (∑ e ∈ G, w e) ≤ ∑ e ∈ G, ∑ v ∈ C, if v ∈ e.val then w e else 0 := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨v, hv⟩ := hC e he
      have hh := Finset.single_le_sum
        (f := fun v => if v ∈ e.val then w e else (0 : ℝ))
        (fun x _ => by split_ifs; exact hw e he; exact le_rfl)
        (Finset.mem_inter.mp hv).2
      simpa [(Finset.mem_inter.mp hv).1] using hh
    _ = ∑ v ∈ C, ∑ e ∈ G, if v ∈ e.val then w e else 0 := Finset.sum_comm
    _ ≤ ∑ _v ∈ C, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hload v)
    _ = (C.card : ℝ) := by simp

/-- Integral cardinality rank dominates every feasible fractional matching. -/
theorem fractional_le_rank (G : Graph V) (hG : (simpleGraph G).Colorable 2)
    (w : Edge V → ℝ) (hw : ∀ e ∈ G, 0 ≤ w e)
    (hload : ∀ v, (∑ e ∈ G, if v ∈ e.val then w e else 0) ≤ 1) :
    (∑ e ∈ G, w e) ≤ (rank G : ℝ) := by
  obtain ⟨M, C, _, _, hC, _, hCr⟩ := project_konig G hG
  rw [← hCr]
  exact fractional_le_cover G w C hw hload hC

/-- An actual integral submatching realizes at least the fractional value. -/
theorem fractional_rounding (G : Graph V) (hG : (simpleGraph G).Colorable 2)
    (w : Edge V → ℝ) (hw : ∀ e ∈ G, 0 ≤ w e)
    (hload : ∀ v, (∑ e ∈ G, if v ∈ e.val then w e else 0) ≤ 1) :
    ∃ M ⊆ G, Matching M ∧ (∑ e ∈ G, w e) ≤ (M.card : ℝ) := by
  obtain ⟨M, hMG, hM, hMc⟩ := rank_attained G
  exact ⟨M, hMG, hM, by rw [hMc]; exact fractional_le_rank G hG w hw hload⟩

end RobustMatching.R7GraphKonig

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphKonig.fractional_rounding
