import RobustMatching.R7ProbabilityPrefix
import RobustMatching.R8AcquisitionProbabilitySuffix

/-! The actual without-replacement probability of an insertion-free epoch.
The event is disjointness of the sampled original labels from a fixed bad set. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8AcquisitionProbability
open RobustMatching.R7ProbabilityPrefix
open RobustMatching.R7ProbabilityPermutation
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem disjoint_image_iff_complement (s T : Finset α) (π : Equiv.Perm α) :
    Disjoint (s.image π) T ↔ T ⊆ sᶜ.image π := by
  constructor
  · intro hd x hx
    apply Finset.mem_image.mpr
    refine ⟨π.symm x,Finset.mem_compl.mpr ?_,π.apply_symm_apply x⟩
    intro hi
    exact Finset.disjoint_left.mp hd
      (Finset.mem_image.mpr ⟨π.symm x,hi,π.apply_symm_apply x⟩) hx
  · intro ht
    apply Finset.disjoint_left.mpr
    intro x hx hT
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj,hje⟩ := Finset.mem_image.mp (ht hT)
    have hij := π.injective (he.trans hje.symm)
    exact Finset.mem_compl.mp hj (hij ▸ hi)

/-- No independence assumption: this is a fraction of actual permutations. -/
theorem permutation_avoid_bound (s T : Finset α) (hn : 0 < Fintype.card α) :
    ((Finset.univ.filter (fun π : Equiv.Perm α => Disjoint (s.image π) T)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤
        ((sᶜ.card : ℝ) / Fintype.card α)^T.card := by
  have he := permutation_image_mean sᶜ (fun u => if T ⊆ u then (1 : ℝ) else 0)
  have hb := subset_probability_le (Finset.univ : Finset α) T
    (Finset.subset_univ _) (by simpa using hn) sᶜ.card
    (by simpa using Finset.card_le_card (Finset.subset_univ sᶜ))
  have hpred (π : Equiv.Perm α) :
      (if Disjoint (s.image π) T then (1 : ℝ) else 0) =
        (if T ⊆ sᶜ.image π then (1 : ℝ) else 0) := by
    simp only [disjoint_image_iff_complement]
  simp only [subsetMean] at he
  simp_rw [←hpred] at he
  simp only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one] at he
  rw [he]
  simpa only [Finset.card_univ] using hb

theorem permutation_avoid_exp (s T : Finset α) (hn : 0 < Fintype.card α) :
    ((Finset.univ.filter (fun π : Equiv.Perm α => Disjoint (s.image π) T)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤
        Real.exp (-(s.card : ℝ)*T.card/Fintype.card α) := by
  have hnR : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
  have hc : (sᶜ.card : ℝ) + s.card = Fintype.card α := by
    exact_mod_cast Finset.card_compl_add_card s
  have hratio : (sᶜ.card : ℝ)/Fintype.card α = 1-(s.card : ℝ)/Fintype.card α := by
    apply (div_eq_iff (ne_of_gt hnR)).mpr
    field_simp
    linarith
  have hexp : (sᶜ.card : ℝ)/Fintype.card α ≤ Real.exp (-(s.card : ℝ)/Fintype.card α) := by
    rw [hratio]
    have hh := Real.add_one_le_exp (-(s.card : ℝ)/Fintype.card α)
    simpa only [neg_div,sub_eq_add_neg,add_comm] using hh
  calc
    _ ≤ ((sᶜ.card : ℝ)/Fintype.card α)^T.card := permutation_avoid_bound s T hn
    _ ≤ (Real.exp (-(s.card : ℝ)/Fintype.card α))^T.card :=
      pow_le_pow_left₀ (by positivity) hexp _
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring

/-- Conditional empty-epoch bound for every fixed observed history, with
the epoch positions and underfull original labels represented in the remaining
label type. Neither their independence nor a conditional sampling law is assumed. -/
theorem cylinder_avoid_exp (s : Finset α) (σ : Equiv.Perm α)
    (B T : Finset (remaining s σ)) (hn : 0 < (remaining s σ).card) :
    ((Finset.univ.filter (fun π : {π : Equiv.Perm α // π ∈ cylinder s σ} =>
      Disjoint (B.image (suffixPermutation s σ π)) T)).card : ℝ) /
        (cylinder s σ).card ≤
      Real.exp (-(B.card : ℝ)*T.card/(remaining s σ).card) := by
  let f : Equiv.Perm (remaining s σ) → ℝ := fun ν =>
    if Disjoint (B.image ν) T then 1 else 0
  have he := (cylinderSuffixEquiv s σ).sum_comp f
  change (∑ π : {π : Equiv.Perm α // π ∈ cylinder s σ},
      if Disjoint (B.image (suffixPermutation s σ π)) T then (1 : ℝ) else 0) =
    ∑ ν : Equiv.Perm (remaining s σ),
      if Disjoint (B.image ν) T then (1 : ℝ) else 0 at he
  simp only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one] at he
  have hc := Fintype.card_congr (cylinderSuffixEquiv s σ)
  simp only [Fintype.card_coe] at hc
  rw [he,hc]
  simpa only [Fintype.card_coe] using permutation_avoid_exp B T (by simpa using hn)

/-- Integrating bounds over an actual finite partition. Used with the
ordered acquisition-prefix map; no independence between histories is required. -/
theorem integrate_fiber_bound {Ω β : Type*} [Fintype Ω] [Fintype β]
    [DecidableEq Ω] [DecidableEq β] (key : Ω → β) (bad : Finset Ω) (p : ℝ)
    (h : ∀ b : β, ((bad.filter (fun x => key x=b)).card : ℝ) ≤
      p * (Finset.univ.filter (fun x => key x=b)).card) :
    (bad.card : ℝ) ≤ p * Fintype.card Ω := by
  have hbad := Finset.sum_card_fiberwise_eq_card_filter bad Finset.univ key
  have hall := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset Ω) Finset.univ key
  simp only [Finset.mem_univ,Finset.filter_true,Finset.card_univ] at hbad hall
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun b _ => h b)
  rw [←Finset.mul_sum] at hr
  have hbR : (∑ b : β, ((bad.filter (fun x => key x=b)).card : ℝ)) = bad.card := by
    exact_mod_cast hbad
  have haR : (∑ b : β, ((Finset.univ.filter (fun x : Ω => key x=b)).card : ℝ)) =
      Fintype.card Ω := by exact_mod_cast hall
  rwa [hbR,haR] at hr

end RobustMatching.R8AcquisitionProbability
