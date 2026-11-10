import RobustMatching.R7ProbabilityPermutation

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RobustMatching.R7ProbabilityStopping
open RobustMatching.R7ProbabilityPermutation

/-- A stopping rule whose decision to stop by k is determined by the first k
observed labels. The underlying sample space consists of actual permutations. -/
def CausalStop {n : ℕ} (τ : Equiv.Perm (Fin n) → ℕ) : Prop :=
  ∀ k σ π, (∀ i : Fin n, i.val < k → σ i = π i) →
    (τ σ ≤ k ↔ τ π ≤ k)

def positions {n : ℕ} (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < k

theorem stop_eq_on_cylinder {n : ℕ} (τ : Equiv.Perm (Fin n) → ℕ)
    (hτ : CausalStop τ) (σ π : Equiv.Perm (Fin n))
    (hπ : π ∈ cylinder (positions (τ σ)) σ) : τ π = τ σ := by
  have hagree : ∀ i : Fin n, i.val < τ σ → σ i = π i := by
    intro i hi
    exact (mem_cylinder.mp hπ i (by simpa [positions] using hi)).symm
  have hle : τ π ≤ τ σ := (hτ (τ σ) σ π hagree).mp le_rfl
  by_contra hne
  have hlt : τ π < τ σ := lt_of_le_of_ne hle hne
  have hsmall : ∀ i : Fin n, i.val < τ π → σ i = π i := by
    intro i hi
    exact hagree i (hi.trans hlt)
  have hback : τ σ ≤ τ π := (hτ (τ π) σ π hsmall).mpr le_rfl
  omega

def stoppedCylinder {n : ℕ} (τ : Equiv.Perm (Fin n) → ℕ)
    (σ : Equiv.Perm (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  (cylinder (positions (τ σ)) σ).filter fun π => τ π = τ σ

theorem stoppedCylinder_eq {n : ℕ} (τ : Equiv.Perm (Fin n) → ℕ)
    (hτ : CausalStop τ) (σ : Equiv.Perm (Fin n)) :
    stoppedCylinder τ σ = cylinder (positions (τ σ)) σ := by
  apply Finset.filter_eq_self.mpr
  intro π hπ
  exact stop_eq_on_cylinder τ hτ σ π hπ

/-- Exact next-label expectation conditional on an ACTUAL stopped prefix.
The only stopping assumption is causality of its decisions, not conditional
uniformity. Uniformity is derived from the permutation-fiber bijection. -/
theorem next_mean_after_stop {n : ℕ} (τ : Equiv.Perm (Fin n) → ℕ)
    (hτ : CausalStop τ) (σ : Equiv.Perm (Fin n)) (hk : τ σ < n)
    (f : Fin n → ℝ) :
    (∑ π ∈ stoppedCylinder τ σ, f (π ⟨τ σ, hk⟩)) /
      (stoppedCylinder τ σ).card =
      (∑ a ∈ remaining (positions (τ σ)) σ, f a) /
        (remaining (positions (τ σ)) σ).card := by
  rw [stoppedCylinder_eq τ hτ σ]
  apply next_mean
  simp [positions]

end RobustMatching.R7ProbabilityStopping

#print axioms RobustMatching.R7ProbabilityStopping.next_mean_after_stop
