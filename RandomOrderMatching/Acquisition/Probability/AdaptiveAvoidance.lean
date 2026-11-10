import RandomOrderMatching.Acquisition.Probability.EpochSampling

/-! Adaptive underfull-set sampling, integrated over every actual ordered
prefix. These theorems assume prefix causality, not a cap-success probability. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Probability.Permutation
variable {α : Type*} [Fintype α] [DecidableEq α]

def prefixKey (s : Finset α) (π : Equiv.Perm α) : s → α := fun j => π j.val

theorem prefixKey_eq_iff (s : Finset α) (σ π : Equiv.Perm α) :
    prefixKey s π = prefixKey s σ ↔ π ∈ cylinder s σ := by
  constructor
  · intro h
    apply mem_cylinder.mpr
    intro j hj
    exact congrFun h ⟨j,hj⟩
  · intro h
    funext j
    exact mem_cylinder.mp h j.val j.property

theorem integrate_cylinder_bound (s : Finset α) (bad : Finset (Equiv.Perm α)) (p : ℝ)
    (h : ∀ σ : Equiv.Perm α, ((bad ∩ cylinder s σ).card : ℝ) ≤ p*(cylinder s σ).card) :
    (bad.card : ℝ)/Fintype.card (Equiv.Perm α) ≤ p := by
  have hf (k : s → α) : ((bad.filter (fun π => prefixKey s π=k)).card : ℝ) ≤
      p*(Finset.univ.filter (fun π => prefixKey s π=k)).card := by
    by_cases hex : ∃ σ : Equiv.Perm α, prefixKey s σ=k
    · obtain ⟨σ,rfl⟩ := hex
      have hfull : (Finset.univ.filter (fun π => prefixKey s π=prefixKey s σ)) = cylinder s σ := by
        ext π
        simp [prefixKey_eq_iff]
      have hbad : bad.filter (fun π => prefixKey s π=prefixKey s σ) = bad ∩ cylinder s σ := by
        ext π
        simp [prefixKey_eq_iff]
      rw [hfull,hbad]
      exact h σ
    · have hn : ∀ π : Equiv.Perm α, prefixKey s π ≠ k := fun π hk => hex ⟨π,hk⟩
      simp [hn]
  have hh := integrate_fiber_bound (prefixKey s) bad p hf
  exact (div_le_iff₀ (by positivity : (0:ℝ)<Fintype.card (Equiv.Perm α))).mpr hh

def badEmptyEpoch (s b : Finset α) (T : Equiv.Perm α → Finset α) (Γ : ℕ) :
    Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun π : Equiv.Perm α => Γ < (T π).card ∧ Disjoint (b.image π) (T π))

/-- The bad set is allowed to depend on all previously seen labels.
An empty epoch with more than Γ still-underfull labels has exponentially small
probability. All probability is the actual finite permutation fraction. -/
theorem adaptive_empty_epoch_bound (s b : Finset α) (hd : Disjoint b s)
    (hb : b.Nonempty) (T : Equiv.Perm α → Finset α) (Γ : ℕ)
    (hT : ∀ π, T π ⊆ remaining s π)
    (hcausal : ∀ σ π, π ∈ cylinder s σ → T π = T σ) :
    ((badEmptyEpoch s b T Γ).card : ℝ)/Fintype.card (Equiv.Perm α) ≤
      Real.exp (-(b.card : ℝ)*Γ/Fintype.card α) := by
  apply integrate_cylinder_bound s
  intro σ
  have hsame : badEmptyEpoch s b T Γ ∩ cylinder s σ =
      (cylinder s σ).filter (fun π : Equiv.Perm α =>
        Γ < (T σ).card ∧ Disjoint (b.image π) (T σ)) := by
    ext π
    simp only [badEmptyEpoch,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨hc,hm⟩,hp⟩
      exact ⟨hp,by simpa only [hcausal σ π hp] using And.intro hc hm⟩
    · rintro ⟨hp,hc,hm⟩
      exact ⟨by simpa only [hcausal σ π hp] using And.intro hc hm,hp⟩
  rw [hsame]
  by_cases hlarge : Γ < (T σ).card
  · simp only [hlarge,true_and]
    have hrem : 0 < (remaining s σ).card := by
      obtain ⟨i,hi⟩ := hb
      exact Finset.card_pos.mpr ⟨σ i,window_image_remaining s b σ hd (Finset.mem_image_of_mem σ hi)⟩
    have hn : 0 < Fintype.card α := lt_of_lt_of_le hrem
      (by simpa using Finset.card_le_card (Finset.subset_univ (remaining s σ)))
    have hremR : (0:ℝ)<(remaining s σ).card := by exact_mod_cast hrem
    have hnR : (0:ℝ)<Fintype.card α := by exact_mod_cast hn
    have hleR : ((remaining s σ).card : ℝ) ≤ Fintype.card α := by
      exact_mod_cast (show (remaining s σ).card ≤ Fintype.card α by
        simpa using Finset.card_le_card (Finset.subset_univ (remaining s σ)))
    have hlargeR : (Γ : ℝ) ≤ (T σ).card := by exact_mod_cast hlarge.le
    have hratio : (Γ : ℝ)/Fintype.card α ≤ (T σ).card/(remaining s σ).card := by
      apply (div_le_div_iff₀ hnR hremR).mpr
      have h1 := mul_le_mul_of_nonneg_left hleR (Nat.cast_nonneg Γ : (0:ℝ)≤Γ)
      have h2 := mul_le_mul_of_nonneg_right hlargeR hnR.le
      exact h1.trans h2
    have hh := cylinder_raw_avoid_exp s b (T σ) σ hd (hT σ) hrem
    have he : -(b.card : ℝ)*(T σ).card/(remaining s σ).card ≤
        -(b.card : ℝ)*Γ/Fintype.card α := by
      have hx := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg b.card : (0:ℝ)≤b.card)
      simpa only [mul_div_assoc,neg_mul,neg_div] using neg_le_neg hx
    have hc : (0:ℝ)<(cylinder s σ).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨σ,sigma_mem_cylinder s σ⟩
    exact (div_le_iff₀ hc).mp (hh.trans (Real.exp_le_exp.mpr he))
  · simp [hlarge]
    positivity

end RandomOrderMatching.Acquisition.Probability
