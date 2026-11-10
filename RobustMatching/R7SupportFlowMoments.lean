import RobustMatching.R7SupportFlowGraph
import RobustMatching.R7SupportFlowLP

/-! Pair-degree moment identities used by the adaptive interval certificate.
The pairing is explicit and injective; no distributional pairing of degree
histograms is assumed. The concrete matrix instantiation remains separate. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlow

theorem pair_endpoint_degree_sum
    {I V : Type*} [Fintype I] [DecidableEq V]
    (u v : I → V) (a : V → ℝ)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hsep : ∀ i j, u i ≠ v j) :
    (∑ x ∈ (Finset.univ.image u ∪ Finset.univ.image v), a x) =
      ∑ i, (a (u i)+a (v i)) := by
  classical
  have hd : Disjoint (Finset.univ.image u) (Finset.univ.image v) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
    exact hsep i j (hi.trans hj.symm)
  rw [Finset.sum_union hd, Finset.sum_image, Finset.sum_image,
    Finset.sum_add_distrib]
  · intro x _ y _ hxy
    exact hv hxy
  · intro x _ y _ hxy
    exact hu hxy

theorem pair_degree_lower_moment
    {I : Type*} [Fintype I] (l r : I → ℝ) (η : ℝ)
    (h : ∀ i, 1-η ≤ l i+r i) :
    (1-η)*(Fintype.card I : ℝ) ≤ ∑ i, (l i+r i) := by
  calc
    (1-η)*(Fintype.card I : ℝ) = ∑ _i : I, (1-η) := by simp; ring
    _ ≤ ∑ i, (l i+r i) := Finset.sum_le_sum fun i _ => h i

theorem pair_degree_upper_moment
    {I : Type*} [Fintype I] (l r : I → ℝ)
    (h : ∀ i, l i+r i ≤ 1) :
    (∑ i, (l i+r i)) ≤ (Fintype.card I : ℝ) := by
  calc
    (∑ i, (l i+r i)) ≤ ∑ _i : I, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card I : ℝ) := by simp

theorem actual_paired_endpoint_lower
    {I V : Type*} [Fintype I] [DecidableEq V]
    (u v : I → V) (a : V → ℝ) (lam η : ℝ)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hsep : ∀ i j, u i ≠ v j)
    (hlam : lam ≤ η) (hdegree : ∀ i, 1-lam ≤ a (u i)+a (v i)) :
    (1-η)*(Fintype.card I : ℝ) ≤
      ∑ x ∈ (Finset.univ.image u ∪ Finset.univ.image v), a x := by
  rw [pair_endpoint_degree_sum u v a hu hv hsep]
  exact pair_degree_lower_moment _ _ η fun i => by
    have hi := hdegree i
    linarith

theorem adaptive_pair_bin_admissible
    {a b ga gb lam η : ℝ}
    (ha : a ≤ ga) (hb : b ≤ gb)
    (hlam : lam ≤ η) (hdegree : 1-lam ≤ a+b) :
    1-η ≤ ga+gb := by linarith

/-- The low unmatched bin uses its load arm. The correct estimate is
a/(1-g) <= 1, not the stronger and generally false estimate <= a. -/
theorem low_bin_load_below_one
    {a g δ : ℝ} (ha : a ≤ 1/2) (hg : g ≤ 1/2) (hδ : 0 < δ) :
    a / max δ (1-g) ≤ 1 := by
  have hm : 0 < max δ (1-g) := lt_of_lt_of_le hδ (le_max_left _ _)
  apply (div_le_iff₀ hm).2
  have hl := le_max_right δ (1-g)
  nlinarith

theorem exact_profile152_finite_margin :
    (((1796442625940517 : ℚ)/2530000000000000 - 1/10000000) *
      (1-2/100000000)) > 71005/100000 := by norm_num

theorem exact_profile198_finite_margin :
    (((3554971459209149039 : ℚ)/5000000000000000000 - 1/10000000) *
      (1-2/100000000)) > 71099/100000 := by norm_num

theorem exact_internal110_finite_margin :
    (((22236564450509 : ℚ)/31250000000000 - 1/10000000) *
      (1-2/100000000)) > 71156/100000 := by norm_num

theorem exact_internal152_finite_margin :
    (((2896371675910694789 : ℚ)/4062500000000000000 - 1/10000000) *
      (1-2/100000000)) > 71295/100000 := by norm_num

theorem bin_capped_weight_lower
    {a g β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hga : g ≤ a) :
    1/(β*max δ (1-g)) ≤ 1/(β*max δ (1-a)) := by
  apply one_div_le_one_div_of_le
  · exact mul_pos hβ (lt_of_lt_of_le hδ (le_max_left _ _))
  · apply mul_le_mul_of_nonneg_left _ hβ.le
    exact max_le_max le_rfl (sub_le_sub_left hga 1)

end RobustMatching.R7SupportFlow

#print axioms RobustMatching.R7SupportFlow.actual_paired_endpoint_lower
#print axioms RobustMatching.R7SupportFlow.adaptive_pair_bin_admissible
#print axioms RobustMatching.R7SupportFlow.low_bin_load_below_one
#print axioms RobustMatching.R7SupportFlow.exact_profile152_finite_margin
#print axioms RobustMatching.R7SupportFlow.exact_profile198_finite_margin
#print axioms RobustMatching.R7SupportFlow.exact_internal110_finite_margin
#print axioms RobustMatching.R7SupportFlow.exact_internal152_finite_margin
#print axioms RobustMatching.R7SupportFlow.bin_capped_weight_lower
