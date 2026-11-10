import RobustMatching.R8AcquisitionProbabilitySampling

/-! Conditional epoch miss probabilities on original-label permutations.
The underfull set may depend on the complete observed prefix, but not on
the future suffix. This module derives its sampling law on each actual fiber. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8AcquisitionProbability
open RobustMatching.R7ProbabilityPermutation
variable {α : Type*} [Fintype α] [DecidableEq α]

def residualSet (s : Finset α) (σ : Equiv.Perm α) (T : Finset α) :
    Finset (remaining s σ) := T.subtype (fun x => x ∈ remaining s σ)

theorem residualSet_image (s : Finset α) (σ : Equiv.Perm α) (T : Finset α)
    (hT : T ⊆ remaining s σ) :
    (residualSet s σ T).image Subtype.val = T := by
  ext x
  simp only [residualSet,Finset.mem_image,Finset.mem_subtype]
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x,hT hx⟩,hx,rfl⟩

theorem residualSet_card (s : Finset α) (σ : Equiv.Perm α) (T : Finset α)
    (hT : T ⊆ remaining s σ) : (residualSet s σ T).card = T.card := by
  have hh := congrArg Finset.card (residualSet_image s σ T hT)
  rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hh

theorem window_image_remaining (s b : Finset α) (σ : Equiv.Perm α)
    (hd : Disjoint b s) : b.image σ ⊆ remaining s σ := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  apply mem_remaining.mpr
  intro hs
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hs
  have heq := σ.injective he
  exact Finset.disjoint_left.mp hd hi (heq ▸ hj)

theorem window_image_extend (s b : Finset α) (σ : Equiv.Perm α)
    (hd : Disjoint b s) (ν : Equiv.Perm (remaining s σ)) :
    b.image (extendSuffix s σ ν).val =
      ((residualSet s σ (b.image σ)).image ν).image Subtype.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hrem := window_image_remaining s b σ hd (Finset.mem_image_of_mem σ hi)
    rw [extendSuffix_apply_remaining s σ ν i hrem]
    apply Finset.mem_image.mpr
    refine ⟨ν ⟨σ i,hrem⟩,?_,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨σ i,hrem⟩,?_,rfl⟩
    simpa only [residualSet,Finset.mem_subtype] using Finset.mem_image_of_mem σ hi
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    have hz' : z.val ∈ b.image σ := by simpa only [residualSet,Finset.mem_subtype] using hz
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hz'
    refine Finset.mem_image.mpr ⟨i,hi,?_⟩
    rw [extendSuffix_apply_remaining s σ ν i (he.symm ▸ z.property)]
    congr 2
    exact Subtype.ext he

theorem disjoint_subtype_images {s : Finset α} {σ : Equiv.Perm α}
    (B T : Finset (remaining s σ)) :
    Disjoint (B.image Subtype.val) (T.image Subtype.val) ↔ Disjoint B T := by
  constructor
  · intro hd
    apply Finset.disjoint_left.mpr
    intro x hx ht
    exact Finset.disjoint_left.mp hd (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ ht)
  · intro hd
    apply Finset.disjoint_left.mpr
    intro x hx ht
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp ht
    have he := Subtype.val_injective hzy
    exact Finset.disjoint_left.mp hd hy (he ▸ hz)

theorem cylinder_raw_avoid_exp (s b T : Finset α) (σ : Equiv.Perm α)
    (hd : Disjoint b s) (hT : T ⊆ remaining s σ)
    (hn : 0 < (remaining s σ).card) :
    (((cylinder s σ).filter (fun π : Equiv.Perm α => Disjoint (b.image π) T)).card : ℝ) /
      (cylinder s σ).card ≤
        Real.exp (-(b.card : ℝ)*T.card/(remaining s σ).card) := by
  let B := residualSet s σ (b.image σ)
  let U := residualSet s σ T
  have hf (ν : Equiv.Perm (remaining s σ)) :
      Disjoint (b.image (extendSuffix s σ ν).val) T ↔ Disjoint (B.image ν) U := by
    rw [window_image_extend s b σ hd ν,←residualSet_image s σ T hT]
    exact disjoint_subtype_images _ _
  have he := cylinder_suffix_mean s σ
    (fun π => if Disjoint (b.image π) T then (1 : ℝ) else 0)
  simp only [hf] at he
  simp only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one] at he
  rw [he]
  have hh := permutation_avoid_exp B U (by simpa using hn)
  have hBc : B.card = b.card := by
    rw [residualSet_card _ _ _ (window_image_remaining s b σ hd),
      Finset.card_image_of_injective _ σ.injective]
  have hUc : U.card = T.card := residualSet_card s σ T hT
  simpa only [hBc,hUc,Fintype.card_coe] using hh

end RobustMatching.R8AcquisitionProbability
