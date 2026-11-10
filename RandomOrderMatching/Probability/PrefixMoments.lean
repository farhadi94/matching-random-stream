import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Operational acquisition ingredients

These results do not formalize the streaming algorithm or its random-permutation
law.  The main probability-facing result proves the product-moment bound from
explicit joint-inclusion bounds on a finite probability space.  Such inclusion
bounds are proved by counting for a uniform fixed-size prefix in the report.
No independence assumption is made.
-/

open scoped BigOperators

namespace RandomOrderMatching.Probability.PrefixMoments

/-- Pointwise domination is all that is needed to charge an adaptive prefix
to a deterministic enclosing prefix. -/
theorem adaptive_prefix_weight_le {ι : Type*} [DecidableEq ι]
    (adaptive enclosing : Finset ι) (a : ι → ℝ)
    (hsub : adaptive ⊆ enclosing) (ha : ∀ i ∈ enclosing, 0 ≤ a i) :
    ∑ i ∈ adaptive, a i ≤ ∑ i ∈ enclosing, a i := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro i hi _
    exact ha i hi)

/-- Inserting a new edge whose old integer endpoint-degree sum is at most
`beta - 2` increases the acquisition potential by at least one. -/
theorem insertion_potential_increase (beta du dv : ℤ)
    (h : du + dv ≤ beta - 2) :
    1 ≤ (2 * beta - 1) - ((du + 1)^2 - du^2) - ((dv + 1)^2 - dv^2) := by
  nlinarith

/-- Deleting an edge with old endpoint-degree sum at least `beta + 1`
increases the same potential by at least one. -/
theorem deletion_potential_increase (beta du dv : ℤ)
    (h : beta + 1 ≤ du + dv) :
    1 ≤ -(2 * beta - 1) - ((du - 1)^2 - du^2) - ((dv - 1)^2 - dv^2) := by
  nlinarith

/-- Indicator-product identity used before taking any expectation. -/
theorem prod_mem_indicator {ι : Type*} [DecidableEq ι]
    (t a : Finset ι) (y : ι → ℝ) :
    (∏ i ∈ t, if i ∈ a then y i else 0) =
      if t ⊆ a then ∏ i ∈ t, y i else 0 := by
  classical
  by_cases ht : t ⊆ a
  · simp only [ht, if_true]
    apply Finset.prod_congr rfl
    intro i hi
    simp [ht hi]
  · simp only [ht, if_false]
    obtain ⟨i, hi, hia⟩ := Finset.not_subset.mp ht
    exact Finset.prod_eq_zero hi (by simp [hia])

/-- A finite-space replacement for the negative-correlation MGF argument.
The hypothesis is only the joint inclusion bound for each fixed subset;
the conclusion controls all nonnegative product weights simultaneously. -/
theorem product_moment_of_inclusion_bounds
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]
    (s : Finset ι) (a : Ω → Finset ι) (p : Ω → ℝ)
    (y : ι → ℝ) (rho : ℝ)
    (hy : ∀ i ∈ s, 0 ≤ y i)
    (hinc : ∀ t ∈ s.powerset,
      (∑ ω, p ω * (if t ⊆ a ω then (1 : ℝ) else 0)) ≤ rho ^ t.card) :
    (∑ ω, p ω * ∏ i ∈ s, (1 + if i ∈ a ω then y i else 0)) ≤
      ∏ i ∈ s, (1 + rho * y i) := by
  classical
  calc
    _ = ∑ t ∈ s.powerset,
        (∑ ω, p ω * (if t ⊆ a ω then (1 : ℝ) else 0)) * ∏ i ∈ t, y i := by
      simp_rw [Finset.prod_one_add, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [prod_mem_indicator]
      split_ifs <;> simp
    _ ≤ ∑ t ∈ s.powerset, rho ^ t.card * ∏ i ∈ t, y i := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_right (hinc t ht)
      exact Finset.prod_nonneg (fun i hi ↦ hy i ((Finset.mem_powerset.mp ht) hi))
    _ = ∏ i ∈ s, (1 + rho * y i) := by
      rw [Finset.prod_one_add]
      apply Finset.sum_congr rfl
      intro t ht
      simp [Finset.prod_mul_distrib]

/-- Exponential majorant after the product-moment step. -/
theorem product_le_exp_sum {ι : Type*} (s : Finset ι)
    (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, (1 + z i) ≤ Real.exp (∑ i ∈ s, z i) := by
  calc
    _ ≤ ∏ i ∈ s, Real.exp (z i) := by
      apply Finset.prod_le_prod
      · intro i hi
        linarith [hz i hi]
      · intro i hi
        linarith [Real.add_one_le_exp (z i)]
    _ = _ := (Real.exp_sum _ _).symm

/-- The finite exponential-moment bound, with abstract nonnegative chord
coefficients `y i ≤ a i / kappa`. This is the algebraic core of batch
prefix matching preservation. -/
theorem batch_prefix_product_bound
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]
    (s : Finset ι) (selected : Ω → Finset ι) (p : Ω → ℝ)
    (y a : ι → ℝ) (rho kappa : ℝ)
    (hrho : 0 ≤ rho) (_hkappa : 0 < kappa)
    (hy : ∀ i ∈ s, 0 ≤ y i)
    (hchord : ∀ i ∈ s, y i ≤ a i / kappa)
    (hinc : ∀ t ∈ s.powerset,
      (∑ ω, p ω * (if t ⊆ selected ω then (1 : ℝ) else 0)) ≤ rho ^ t.card) :
    (∑ ω, p ω * ∏ i ∈ s, (1 + if i ∈ selected ω then y i else 0)) ≤
      Real.exp (rho * (∑ i ∈ s, a i) / kappa) := by
  calc
    _ ≤ ∏ i ∈ s, (1 + rho * y i) :=
      product_moment_of_inclusion_bounds s selected p y rho hy hinc
    _ ≤ Real.exp (∑ i ∈ s, rho * y i) :=
      product_le_exp_sum s _ (fun i hi ↦ mul_nonneg hrho (hy i hi))
    _ ≤ Real.exp (rho * (∑ i ∈ s, a i) / kappa) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ∑ i ∈ s, rho * (a i / kappa) :=
          Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (hchord i hi) hrho)
        _ = _ := by simp [Finset.mul_sum, Finset.sum_div, mul_div_assoc]

/-- The chord of `2^x` on `[0,1]`, supplying the coefficient hypothesis above. -/
theorem two_rpow_sub_one_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (2 : ℝ) ^ x - 1 ≤ x := by
  have h := (convexOn_rpow_left (by norm_num : (0 : ℝ) < 2)).2
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - x by linarith) hx0 (show (1 - x) + x = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.rpow_zero,
    Real.rpow_one] at h
  linarith

/-- Batch-prefix MGF under the primitive joint-inclusion inequalities.
The coefficient `a i` can count matching edges in a batch; its upper bound is
`kappa`, not one. The finite probability weights need not be independent. -/
theorem batch_prefix_mgf
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]
    (s : Finset ι) (selected : Ω → Finset ι) (p : Ω → ℝ)
    (a : ι → ℝ) (rho kappa : ℝ)
    (hrho : 0 ≤ rho) (hkappa : 0 < kappa)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (hak : ∀ i ∈ s, a i ≤ kappa)
    (hinc : ∀ t ∈ s.powerset,
      (∑ ω, p ω * (if t ⊆ selected ω then (1 : ℝ) else 0)) ≤ rho ^ t.card) :
    (∑ ω, p ω * (2 : ℝ) ^
      ((∑ i ∈ s, if i ∈ selected ω then a i else 0) / kappa)) ≤
      Real.exp (rho * (∑ i ∈ s, a i) / kappa) := by
  have h := batch_prefix_product_bound s selected p
    (fun i ↦ (2 : ℝ) ^ (a i / kappa) - 1) a rho kappa hrho hkappa
    (fun i hi ↦ sub_nonneg.mpr
      (Real.one_le_rpow (by norm_num) (div_nonneg (ha0 i hi) hkappa.le)))
    (fun i hi ↦ two_rpow_sub_one_le _ (div_nonneg (ha0 i hi) hkappa.le)
      ((div_le_one hkappa).mpr (hak i hi))) hinc
  convert h using 1
  apply Finset.sum_congr rfl
  intro ω hω
  congr 1
  rw [Finset.sum_div, Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp

/-- A final deterministic implication converts prefix loss to preservation
of any witness size. It is independent of how the freeze time was selected. -/
theorem preserved_witness_bound (mu lost retained rho : ℝ)
    (hloss : lost ≤ 2 * rho * mu) (hkeep : mu - lost ≤ retained) :
    (1 - 2 * rho) * mu ≤ retained := by
  nlinarith

/-- Sampling without replacement only decreases the probability of repeatedly
selecting from a fixed initial segment. This is the falling-factorial form. -/
theorem descending_factorial_ratio_le (ell q s : ℕ)
    (hq : 0 < q) (helq : ell ≤ q) (hs : s ≤ ell) :
    (ell.descFactorial s : ℝ) / (q.descFactorial s : ℝ) ≤
      ((ell : ℝ) / q) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hsel : s < ell := Nat.lt_of_succ_le hs
    have hsq : s < q := lt_of_lt_of_le hsel helq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hqsR : (0 : ℝ) < q - s := by
      have hsqR : (s : ℝ) < q := by exact_mod_cast hsq
      linarith
    have hratio : ((ell - s : ℕ) : ℝ) / ((q - s : ℕ) : ℝ) ≤ (ell : ℝ) / q := by
      rw [Nat.cast_sub hsel.le, Nat.cast_sub hsq.le]
      apply (div_le_div_iff₀ hqsR hqR).mpr
      have hsqR : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      have hleR : (ell : ℝ) ≤ q := by exact_mod_cast helq
      nlinarith
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_mul, mul_div_mul_comm, pow_succ']
    exact mul_le_mul hratio (ih (Nat.le_of_lt hsel))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The binomial expression for the joint inclusion probability equals the
falling-factorial ratio. All denominator nonzero obligations are explicit. -/
theorem choose_inclusion_ratio (q ell s : ℕ) (helq : ell ≤ q) (hs : s ≤ ell) :
    ((q - s).choose (ell - s) : ℝ) / (q.choose ell : ℝ) =
      (ell.descFactorial s : ℝ) / (q.descFactorial s : ℝ) := by
  have hsQ : s ≤ q := hs.trans helq
  have hqell : (q.choose ell : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero helq
  have hqs : (q.choose s : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hsQ
  have hfact : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
  have hchoose : (q.choose ell : ℝ) * (ell.choose s : ℝ) =
      (q.choose s : ℝ) * ((q-s).choose (ell-s) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := q) hs
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_left _ _ hfact]
  apply (div_eq_div_iff hqell hqs).mpr
  nlinarith

/-- Exact uniform fixed-size subset inclusion bound, stated as a ratio of
finite cardinalities. This discharges the combinatorial sampling inequality
used by the MGF proof; connecting a permutation prefix to this uniform subset
law is a separate permutation-symmetry fact. -/
theorem uniform_subset_inclusion_le {ι : Type*} [DecidableEq ι]
    (population required : Finset ι) (ell : ℕ)
    (hq : 0 < population.card) (helq : ell ≤ population.card)
    (hsub : required ⊆ population) :
    (((population.powersetCard ell).filter (required ⊆ ·)).card : ℝ) /
        ((population.powersetCard ell).card : ℝ) ≤
      ((ell : ℝ) / population.card) ^ required.card := by
  by_cases hs : required.card ≤ ell
  · rw [Finset.card_filter_powersetCard_subset required population ell hsub hs,
      Finset.card_powersetCard, choose_inclusion_ratio _ _ _ helq hs]
    exact descending_factorial_ratio_le ell population.card required.card hq helq hs
  · have hempty : (population.powersetCard ell).filter (required ⊆ ·) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro selected hselected hrequired
      have hcard := Finset.card_le_card hrequired
      have hselectedCard := (Finset.mem_powersetCard.mp hselected).2
      exact hs (hselectedCard ▸ hcard)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

/-- Markov's inequality on a finite weighted sample space. Normalization of
`p` is not needed for the inequality, so it is stated at its exact scope. -/
theorem finite_markov {Ω : Type*} [Fintype Ω]
    (p Y : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hY : ∀ ω, 0 ≤ Y ω)
    (threshold : ℝ) (ht : 0 < threshold) :
    (∑ ω, p ω * (if threshold ≤ Y ω then (1 : ℝ) else 0)) ≤
      (∑ ω, p ω * Y ω) / threshold := by
  classical
  apply (le_div_iff₀ ht).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : threshold ≤ Y ω
  · simpa [h] using mul_le_mul_of_nonneg_left h (hp ω)
  · simp only [h, if_false, mul_zero, zero_mul]
    exact mul_nonneg (hp ω) (hY ω)

/-- An actual finite tail bound for batch prefix weight. The sampling input is
the joint-inclusion law, not an assumed concentration conclusion. -/
theorem batch_prefix_tail
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]
    (s : Finset ι) (selected : Ω → Finset ι) (p : Ω → ℝ)
    (a : ι → ℝ) (rho kappa cutoff : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hrho : 0 ≤ rho) (hkappa : 0 < kappa)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (hak : ∀ i ∈ s, a i ≤ kappa)
    (hinc : ∀ t ∈ s.powerset,
      (∑ ω, p ω * (if t ⊆ selected ω then (1 : ℝ) else 0)) ≤ rho ^ t.card) :
    (∑ ω, p ω * (if cutoff ≤ (∑ i ∈ s, if i ∈ selected ω then a i else 0)
      then (1 : ℝ) else 0)) ≤
      Real.exp (rho * (∑ i ∈ s, a i) / kappa) / (2 : ℝ) ^ (cutoff / kappa) := by
  classical
  let X : Ω → ℝ := fun ω ↦ ∑ i ∈ s, if i ∈ selected ω then a i else 0
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hthreshold : 0 < (2 : ℝ) ^ (cutoff / kappa) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h := finite_markov p (fun ω ↦ (2 : ℝ) ^ (X ω / kappa)) hp
    (fun _ ↦ Real.rpow_nonneg (by norm_num) _)
    ((2 : ℝ) ^ (cutoff / kappa)) hthreshold
  have hpred (ω : Ω) : (2 : ℝ) ^ (cutoff / kappa) ≤ (2 : ℝ) ^ (X ω / kappa) ↔
      cutoff ≤ X ω := by
    rw [Real.rpow_le_rpow_left_iff htwo, div_le_div_iff_of_pos_right hkappa]
  simp_rw [hpred] at h
  exact h.trans (div_le_div_of_nonneg_right
    (batch_prefix_mgf s selected p a rho kappa hrho hkappa ha0 hak hinc) hthreshold.le)

/-- Ordered completions of a fixed prefix are in bijection with all orders of
the remaining labels. This is the combinatorial core of suffix uniformity;
no conditioning on an order-dependent future event is built into the type. -/
def fixedPrefixCompletionEquiv {ι : Type*} (pre remainder : List ι) :
    {whole : List ι // whole.Perm (pre ++ remainder) ∧
      whole.take pre.length = pre} ≃
    {tail : List ι // tail.Perm remainder} where
  toFun whole := ⟨whole.val.drop pre.length, by
    have heq : pre ++ whole.val.drop pre.length = whole.val := by
      calc
        _ = whole.val.take pre.length ++ whole.val.drop pre.length := by rw [whole.property.2]
        _ = _ := List.take_append_drop pre.length whole.val
    have hperm : (pre ++ whole.val.drop pre.length).Perm (pre ++ remainder) := by
      rw [heq]
      exact whole.property.1
    exact (List.perm_append_left_iff pre).mp hperm⟩
  invFun tail := ⟨pre ++ tail.val, ⟨List.Perm.append_left pre tail.property, by simp⟩⟩
  left_inv whole := by
    apply Subtype.ext
    change pre ++ whole.val.drop pre.length = whole.val
    calc
      _ = whole.val.take pre.length ++ whole.val.drop pre.length := by rw [whole.property.2]
      _ = _ := List.take_append_drop pre.length whole.val
  right_inv tail := by
    apply Subtype.ext
    simp

end RandomOrderMatching.Probability.PrefixMoments

#print axioms RandomOrderMatching.Probability.PrefixMoments.adaptive_prefix_weight_le
#print axioms RandomOrderMatching.Probability.PrefixMoments.insertion_potential_increase
#print axioms RandomOrderMatching.Probability.PrefixMoments.deletion_potential_increase
#print axioms RandomOrderMatching.Probability.PrefixMoments.product_moment_of_inclusion_bounds
#print axioms RandomOrderMatching.Probability.PrefixMoments.batch_prefix_product_bound
#print axioms RandomOrderMatching.Probability.PrefixMoments.batch_prefix_mgf
#print axioms RandomOrderMatching.Probability.PrefixMoments.uniform_subset_inclusion_le
#print axioms RandomOrderMatching.Probability.PrefixMoments.batch_prefix_tail
#print axioms RandomOrderMatching.Probability.PrefixMoments.fixedPrefixCompletionEquiv
