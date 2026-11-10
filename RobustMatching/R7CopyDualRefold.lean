import RobustMatching.R7CopyDualHungarian
import RobustMatching.R6FableSharpDualCopy

/-! Exact bipartite refolding of arbitrary retained copies. This is an
unconditional graph theorem: both the original matching and the integral
price witness are constructed by the finite Hall theorem. -/
open scoped BigOperators
noncomputable section
namespace RobustMatching.R7CopyDual
open RobustMatching.Dual RobustMatching.R6FableSharpDualCopy
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem copy_matching_refolds (W : ℕ) (E : Finset (L × R)) (w : L × R → ℕ)
    (C : Finset ((L × Fin W) × (R × Fin W)))
    (hC : IsMatching C) (hsub : ∀ e ∈ C, e ∈ CopyEdges W (E : Set (L × R)) w) :
    ∃ M : Finset (L × R), IsMatching M ∧ M ⊆ E ∧ C.card ≤ ∑ e ∈ M, w e := by
  obtain ⟨M,p,q,hM,hME,hfeas,hcost⟩ := exists_nat_bipartite_dual E w
  have hf := bottom_covers W (E : Set (L × R)) w p q hfeas
  have hempty : IsMatching (∅ : Finset ((L × Fin W) × (R × Fin W))) := by
    constructor <;> simp [Set.InjOn]
  have hb := deletion_left_bound hf hC hempty hsub (by simp)
  have hbc := bottom_cost_le W p q
  simp only [Finset.sum_const,Finset.sum_empty,nsmul_eq_mul,mul_one,add_zero] at hb
  have hc : ((∑ e ∈ M, w e : ℕ) : ℝ) =
      (∑ l, (p l : ℝ)) + ∑ r, (q r : ℝ) := by exact_mod_cast hcost
  refine ⟨M,hM,hME,?_⟩
  have hreal : (C.card : ℝ) ≤ ((∑ e ∈ M, w e : ℕ) : ℝ) := by linarith
  exact_mod_cast hreal

/-- Refolding uses only the original parents of the retained copies. -/
theorem retained_copy_matching_refolds (W : ℕ) (w : L × R → ℕ)
    (C : Finset ((L × Fin W) × (R × Fin W)))
    (hC : IsMatching C)
    (hidx : ∀ e ∈ C, e.1.2.val + e.2.2.val + 1 = w (e.1.1,e.2.1)) :
    ∃ M : Finset (L × R), IsMatching M ∧
      M ⊆ C.image (fun e => (e.1.1,e.2.1)) ∧ C.card ≤ ∑ e ∈ M, w e := by
  apply copy_matching_refolds W _ w C hC
  intro e he
  exact ⟨Finset.mem_image_of_mem _ he,hidx e he⟩

end RobustMatching.R7CopyDual
#print axioms RobustMatching.R7CopyDual.copy_matching_refolds
#print axioms RobustMatching.R7CopyDual.retained_copy_matching_refolds
