import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RobustMatching.R7ProbabilityPermutation

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A concrete ordered-prefix cylinder in the finite uniform permutation space.
`s` is the set of exposed positions and `σ` records their observed labels. -/
def cylinder (s : Finset α) (σ : Equiv.Perm α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun π => ∀ j ∈ s, π j = σ j

def remaining (s : Finset α) (σ : Equiv.Perm α) : Finset α :=
  Finset.univ \ s.image σ

def nextFiber (s : Finset α) (σ : Equiv.Perm α) (i a : α) :
    Finset (Equiv.Perm α) :=
  (cylinder s σ).filter fun π => π i = a

theorem mem_cylinder {s : Finset α} {σ π : Equiv.Perm α} :
    π ∈ cylinder s σ ↔ ∀ j ∈ s, π j = σ j := by
  simp [cylinder]

theorem mem_remaining {s : Finset α} {σ : Equiv.Perm α} {a : α} :
    a ∈ remaining s σ ↔ a ∉ s.image σ := by
  simp [remaining]

theorem mem_nextFiber {s : Finset α} {σ π : Equiv.Perm α} {i a : α} :
    π ∈ nextFiber s σ i a ↔ (∀ j ∈ s, π j = σ j) ∧ π i = a := by
  simp [nextFiber, mem_cylinder]

theorem next_mem_remaining {s : Finset α} {σ π : Equiv.Perm α} {i : α}
    (hi : i ∉ s) (hπ : π ∈ cylinder s σ) : π i ∈ remaining s σ := by
  rw [mem_remaining]
  intro h
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
  have hp := mem_cylinder.mp hπ j hj
  have : j = i := π.injective (hp.trans he)
  exact hi (this ▸ hj)

theorem sigma_mem_cylinder (s : Finset α) (σ : Equiv.Perm α) :
    σ ∈ cylinder s σ := by simp [cylinder]

/-- Swapping two unexposed labels preserves every observed position. -/
theorem swap_mem_cylinder {s : Finset α} {σ π : Equiv.Perm α} {a b : α}
    (ha : a ∈ remaining s σ) (hb : b ∈ remaining s σ)
    (hπ : π ∈ cylinder s σ) :
    π.trans (Equiv.swap a b) ∈ cylinder s σ := by
  apply mem_cylinder.mpr
  intro j hj
  change Equiv.swap a b (π j) = σ j
  rw [mem_cylinder.mp hπ j hj]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact mem_remaining.mp ha (h ▸ Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  · intro h
    exact mem_remaining.mp hb (h ▸ Finset.mem_image.mpr ⟨j, hj, rfl⟩)

/-- Actual next-label fibers of a uniform permutation cylinder are equinumerous.
The proof constructs a label-swap bijection; no conditional-uniformity law is
assumed. -/
theorem nextFiber_card_eq {s : Finset α} {σ : Equiv.Perm α} {i a b : α}
    (ha : a ∈ remaining s σ) (hb : b ∈ remaining s σ) :
    (nextFiber s σ i a).card = (nextFiber s σ i b).card := by
  apply Finset.card_bij (fun π _ => π.trans (Equiv.swap a b))
  · intro π hπ
    obtain ⟨hc, hn⟩ := Finset.mem_filter.mp hπ
    apply Finset.mem_filter.mpr
    refine ⟨swap_mem_cylinder ha hb hc, ?_⟩
    change Equiv.swap a b (π i) = b
    rw [hn, Equiv.swap_apply_left]
  · intro π₁ _ π₂ _ h
    apply Equiv.ext
    intro j
    have hj := congrArg (fun e : Equiv.Perm α => e j) h
    exact (Equiv.swap a b).injective hj
  · intro π hπ
    refine ⟨π.trans (Equiv.swap a b), ?_, ?_⟩
    · obtain ⟨hc, hn⟩ := Finset.mem_filter.mp hπ
      apply Finset.mem_filter.mpr
      refine ⟨swap_mem_cylinder ha hb hc, ?_⟩
      change Equiv.swap a b (π i) = a
      rw [hn, Equiv.swap_apply_right]
    · ext j
      exact Equiv.swap_apply_self a b (π j)

theorem cylinder_card_eq {s : Finset α} {σ : Equiv.Perm α} {i a : α}
    (hi : i ∉ s) (ha : a ∈ remaining s σ) :
    (cylinder s σ).card = (remaining s σ).card * (nextFiber s σ i a).card := by
  have hmap : (cylinder s σ : Set (Equiv.Perm α)).MapsTo
      (fun π => π i) (remaining s σ) := fun _ hπ => next_mem_remaining hi hπ
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ = ∑ _b ∈ remaining s σ, (nextFiber s σ i a).card := by
      apply Finset.sum_congr rfl
      intro b hb
      exact nextFiber_card_eq hb ha
    _ = _ := by simp

/-- The exact conditional next-label expectation under a uniform permutation,
written as finite averages on its actual prefix cylinder. -/
theorem next_mean {s : Finset α} {σ : Equiv.Perm α} {i : α}
    (hi : i ∉ s) (f : α → ℝ) :
    (∑ π ∈ cylinder s σ, f (π i)) / (cylinder s σ).card =
      (∑ a ∈ remaining s σ, f a) / (remaining s σ).card := by
  have ha : σ i ∈ remaining s σ := next_mem_remaining hi (sigma_mem_cylinder s σ)
  have hmap : (cylinder s σ : Set (Equiv.Perm α)).MapsTo
      (fun π => π i) (remaining s σ) := fun _ hπ => next_mem_remaining hi hπ
  have hc : 0 < (cylinder s σ).card := Finset.card_pos.mpr ⟨σ, sigma_mem_cylinder s σ⟩
  have hcard := cylinder_card_eq hi ha
  have hfib : 0 < (nextFiber s σ i (σ i)).card := by
    apply Finset.card_pos.mpr
    exact ⟨σ, mem_nextFiber.mpr ⟨by intro j _; rfl, rfl⟩⟩
  have hsum : (∑ π ∈ cylinder s σ, f (π i)) =
      ((nextFiber s σ i (σ i)).card : ℝ) * ∑ a ∈ remaining s σ, f a := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    calc
      _ = ∑ a ∈ remaining s σ,
          ((nextFiber s σ i (σ i)).card : ℝ) * f a := by
        apply Finset.sum_congr rfl
        intro a ha'
        have he : ∀ π ∈ (cylinder s σ).filter (fun π => π i = a), f (π i) = f a := by
          intro π hπ
          rw [(Finset.mem_filter.mp hπ).2]
        rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
        change ((nextFiber s σ i a).card : ℝ) * f a = _
        rw [nextFiber_card_eq ha' ha]
      _ = _ := by rw [Finset.mul_sum]
  rw [hsum, hcard, Nat.cast_mul]
  have hz : ((nextFiber s σ i (σ i)).card : ℝ) ≠ 0 := by positivity
  field_simp

end RobustMatching.R7ProbabilityPermutation

#print axioms RobustMatching.R7ProbabilityPermutation.nextFiber_card_eq
#print axioms RobustMatching.R7ProbabilityPermutation.next_mean
