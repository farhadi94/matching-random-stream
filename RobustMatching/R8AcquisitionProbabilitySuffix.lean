import RobustMatching.R7ProbabilityStopping

/-! Full suffix law on a concrete ordered-prefix cylinder. The equivalence
permutes exactly the unexposed original labels, fixing every exposed label. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8AcquisitionProbability
open RobustMatching.R7ProbabilityPermutation RobustMatching.R7ProbabilityStopping
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem relative_remaining (s : Finset α) (σ π : Equiv.Perm α)
    (hπ : π ∈ cylinder s σ) (x : α) :
    (σ.symm.trans π) x ∈ remaining s σ ↔ x ∈ remaining s σ := by
  have hfix (j : α) (hj : j ∈ s) : (σ.symm.trans π) (σ j) = σ j := by
    simpa using mem_cylinder.mp hπ j hj
  have heq : (σ.symm.trans π) x ∈ s.image σ ↔ x ∈ s.image σ := by
    constructor
    · intro hx
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hx
      have h := (σ.symm.trans π).injective ((hfix j hj).trans he)
      exact h ▸ Finset.mem_image_of_mem σ hj
    · intro hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      rw [hfix j hj]
      exact Finset.mem_image_of_mem σ hj
  simpa only [mem_remaining] using not_congr heq

def suffixPermutation (s : Finset α) (σ : Equiv.Perm α)
    (π : {π : Equiv.Perm α // π ∈ cylinder s σ}) : Equiv.Perm (remaining s σ) :=
  Equiv.Perm.subtypePerm (σ.symm.trans π.val) (relative_remaining s σ π.val π.property)

def extendSuffix (s : Finset α) (σ : Equiv.Perm α)
    (τ : Equiv.Perm (remaining s σ)) : {π : Equiv.Perm α // π ∈ cylinder s σ} :=
  ⟨σ.trans (Equiv.Perm.ofSubtype τ), by
    apply mem_cylinder.mpr
    intro j hj
    change Equiv.Perm.ofSubtype τ (σ j) = σ j
    exact Equiv.Perm.ofSubtype_apply_of_not_mem τ
      (fun h => mem_remaining.mp h (Finset.mem_image_of_mem σ hj))⟩

theorem extendSuffix_apply_remaining (s : Finset α) (σ : Equiv.Perm α)
    (τ : Equiv.Perm (remaining s σ)) (j : α) (hj : σ j ∈ remaining s σ) :
    (extendSuffix s σ τ).val j = (τ ⟨σ j,hj⟩).val := by
  exact Equiv.Perm.ofSubtype_apply_of_mem τ hj

def cylinderSuffixEquiv (s : Finset α) (σ : Equiv.Perm α) :
    {π : Equiv.Perm α // π ∈ cylinder s σ} ≃ Equiv.Perm (remaining s σ) where
  toFun := suffixPermutation s σ
  invFun := extendSuffix s σ
  left_inv π := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : σ i ∈ remaining s σ
    · rw [extendSuffix_apply_remaining s σ _ i hi]
      simp [suffixPermutation,Equiv.Perm.subtypePerm_apply]
    · have hs : i ∈ s := by
        have hx : σ i ∈ s.image σ := by simpa only [mem_remaining,not_not] using hi
        simpa only [Finset.mem_image,σ.injective.eq_iff,exists_eq_right] using hx
      have he := mem_cylinder.mp π.property i hs
      change Equiv.Perm.ofSubtype _ (σ i) = π.val i
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hi,he]
  right_inv τ := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (extendSuffix s σ τ).val (σ.symm x.val) = (τ x).val
    change Equiv.Perm.ofSubtype τ (σ (σ.symm x.val)) = (τ x).val
    rw [σ.apply_symm_apply,Equiv.Perm.ofSubtype_apply_coe]

/-- Equality for every real test function is the complete conditional suffix
law, not merely the one-step marginal. The original residual labels are explicit. -/
theorem cylinder_suffix_mean (s : Finset α) (σ : Equiv.Perm α)
    (f : Equiv.Perm α → ℝ) :
    (∑ π ∈ cylinder s σ, f π) / (cylinder s σ).card =
      (∑ τ : Equiv.Perm (remaining s σ), f (extendSuffix s σ τ).val) /
        Fintype.card (Equiv.Perm (remaining s σ)) := by
  have hsum := (cylinderSuffixEquiv s σ).symm.sum_comp (fun π => f π.val)
  change (∑ τ : Equiv.Perm (remaining s σ), f (extendSuffix s σ τ).val) =
    ∑ π : {π : Equiv.Perm α // π ∈ cylinder s σ}, f π.val at hsum
  have hc := Fintype.card_congr (cylinderSuffixEquiv s σ)
  simp only [Fintype.card_coe] at hc
  rw [← hc]
  congr 1
  simpa only [Finset.sum_coe_sort] using hsum.symm

/-- At a causal freeze, conditioning on the stop adds no restriction to the
unobserved labels. The entire suffix, with original batch labels intact, is
uniform over all residual-label permutations. -/
theorem stopped_suffix_mean {n : ℕ} (τ : Equiv.Perm (Fin n) → ℕ)
    (hτ : CausalStop τ) (σ : Equiv.Perm (Fin n))
    (f : Equiv.Perm (Fin n) → ℝ) :
    (∑ π ∈ stoppedCylinder τ σ, f π) / (stoppedCylinder τ σ).card =
      (∑ ν : Equiv.Perm (remaining (positions (τ σ)) σ),
        f (extendSuffix (positions (τ σ)) σ ν).val) /
          Fintype.card (Equiv.Perm (remaining (positions (τ σ)) σ)) := by
  rw [stoppedCylinder_eq τ hτ σ]
  exact cylinder_suffix_mean _ _ _

end RobustMatching.R8AcquisitionProbability
