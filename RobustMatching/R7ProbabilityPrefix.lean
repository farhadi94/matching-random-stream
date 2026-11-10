import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RobustMatching.R7ProbabilityPrefix

/-- Sampling without replacement can only reduce the probability of containing
a fixed set, compared with independent inclusion at the same marginal rate. -/
theorem desc_ratio_le (n k t : ℕ) (hn : 0 < n) (hk : k ≤ n) (ht : t ≤ k) :
    (k.descFactorial t : ℝ) / (n.descFactorial t : ℝ) ≤
      ((k : ℝ)/(n : ℝ))^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htk : t ≤ k := by omega
    have htn : t < n := by omega
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have htnR : (t:ℝ) < n := by exact_mod_cast htn
    have hnt : (0:ℝ) < n-t := by linarith
    have htR : (0:ℝ) ≤ t := by positivity
    have hkn : (k:ℝ) ≤ n := by exact_mod_cast hk
    have hkt : (t:ℝ) ≤ k := by exact_mod_cast htk
    have hf : ((k:ℝ)-t)/(n-t) ≤ (k:ℝ)/n := by
      apply (div_le_div_iff₀ hnt hnR).mpr
      nlinarith
    have hfac : 0 ≤ ((k:ℝ)-t)/(n-t) := div_nonneg (sub_nonneg.mpr hkt) hnt.le
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_sub htk, Nat.cast_sub (by omega : t ≤ n),
      mul_div_mul_comm, pow_succ]
    calc
      _ ≤ (((k:ℝ)-t)/(n-t))*((k:ℝ)/n)^t :=
        mul_le_mul_of_nonneg_left (ih htk) hfac
      _ ≤ ((k:ℝ)/n)^t*((k:ℝ)/n) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hf
          (pow_nonneg (div_nonneg (by positivity : (0:ℝ) ≤ k) hnR.le) t)

theorem choose_ratio_le (n k t : ℕ) (hn : 0 < n) (hk : k ≤ n) (ht : t ≤ k) :
    ((n-t).choose (k-t) : ℝ)/(n.choose k : ℝ) ≤ ((k:ℝ)/n)^t := by
  have hnt : t ≤ n := ht.trans hk
  have hchoose : (n.choose k : ℝ)*(k.choose t : ℝ) =
      (n.choose t : ℝ)*((n-t).choose (k-t) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := n) ht
  have hc1 : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hc2 : (n.choose t : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hnt).ne'
  have hfact : (t.factorial:ℝ) ≠ 0 := by positivity
  have heq : ((n-t).choose (k-t) : ℝ)/(n.choose k : ℝ) =
      (k.descFactorial t : ℝ)/(n.descFactorial t : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
    nlinarith [hchoose]
  rw [heq]
  exact desc_ratio_le n k t hn hk ht

variable {α : Type*} [DecidableEq α]

/-- Exact finite-space upper bound for the inclusion probability of any fixed
subset in a uniformly chosen k-subset. -/
theorem subset_probability_le (s t : Finset α) (hst : t ⊆ s)
    (hn : 0 < s.card) (k : ℕ) (hk : k ≤ s.card) :
    (((s.powersetCard k).filter (t ⊆ ·)).card : ℝ) /
      ((s.powersetCard k).card : ℝ) ≤ ((k:ℝ)/s.card)^t.card := by
  by_cases htk : t.card ≤ k
  · rw [Finset.card_filter_powersetCard_subset t s k hst htk,
      Finset.card_powersetCard]
    exact choose_ratio_le s.card k t.card hn hk htk
  · have hempty : (s.powersetCard k).filter (t ⊆ ·) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hu, htu⟩ := Finset.mem_filter.mp hu
      have hc := (Finset.mem_powersetCard.mp hu).2
      have hh := Finset.card_le_card htu
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

def subsetMean (s : Finset α) (k : ℕ) (f : Finset α → ℝ) : ℝ :=
  (∑ u ∈ s.powersetCard k, f u) / ((s.powersetCard k).card : ℝ)

theorem product_expansion (s : Finset α) (k : ℕ) (z : α → ℝ) :
    subsetMean s k (fun u => ∏ x ∈ u, (z x+1)) =
      ∑ t ∈ s.powerset,
        ((((s.powersetCard k).filter (t ⊆ ·)).card : ℝ) /
          ((s.powersetCard k).card : ℝ)) * ∏ x ∈ t, z x := by
  classical
  have hpow (u : Finset α) (hu : u ∈ s.powersetCard k) :
      u.powerset = s.powerset.filter (· ⊆ u) := by
    ext t
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨h.trans (Finset.mem_powersetCard.mp hu).1, h⟩, And.right⟩
  unfold subsetMean
  simp_rw [Finset.prod_add_one]
  have hh : (∑ u ∈ s.powersetCard k, ∑ t ∈ u.powerset, ∏ x ∈ t, z x) =
      ∑ t ∈ s.powerset, ∑ u ∈ s.powersetCard k,
        if t ⊆ u then ∏ x ∈ t, z x else 0 := by
    rw [← Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hpow u hu, Finset.sum_filter]
  rw [hh, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem subset_product_le (s : Finset α) (k : ℕ) (hn : 0 < s.card)
    (hk : k ≤ s.card) (z : α → ℝ) (hz : ∀ x ∈ s, 0 ≤ z x) :
    subsetMean s k (fun u => ∏ x ∈ u, (z x+1)) ≤
      ∏ x ∈ s, (((k:ℝ)/s.card)*z x+1) := by
  rw [product_expansion, Finset.prod_add_one]
  apply Finset.sum_le_sum
  intro t ht
  have hts := Finset.mem_powerset.mp ht
  have hp : 0 ≤ ∏ x ∈ t, z x := Finset.prod_nonneg fun x hx => hz x (hts hx)
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  exact mul_le_mul_of_nonneg_right (subset_probability_le s t hts hn k hk) hp

/-- A moment bound for the actual uniform k-subset sample space. This is the
without-replacement Bernoulli-product bound, proved by inclusion counts. -/
theorem subset_exp_le_product (s : Finset α) (k : ℕ) (hn : 0 < s.card)
    (hk : k ≤ s.card) (r : α → ℝ) (hr : ∀ x ∈ s, 0 ≤ r x)
    (t : ℝ) (ht : 0 ≤ t) :
    subsetMean s k (fun u => Real.exp (t * ∑ x ∈ u, r x)) ≤
      ∏ x ∈ s, (1+((k:ℝ)/s.card)*(Real.exp (t*r x)-1)) := by
  have hleft (u : Finset α) :
      Real.exp (t*∑ x ∈ u, r x) = ∏ x ∈ u, ((Real.exp (t*r x)-1)+1) := by
    simp only [sub_add_cancel]
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hleft]
  simpa only [add_comm] using subset_product_le s k hn hk
    (fun x => Real.exp (t*r x)-1)
    (fun x hx => sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg ht (hr x hx))))

section Permutation
variable [Fintype α]

def imageFiber (s t : Finset α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun π => s.image π = t

omit [Fintype α] in
theorem image_trans (s : Finset α) (π τ : Equiv.Perm α) :
    s.image (π.trans τ) = (s.image π).image τ := by
  rw [Finset.image_image]
  rfl

theorem imageFiber_card_eq (s t u : Finset α) (h : t.card = u.card) :
    (imageFiber s t).card = (imageFiber s u).card := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq t u h
  have hτ' : t.image τ = u := by
    rw [Finset.map_eq_image] at hτ
    exact hτ
  have hτinv : u.image τ.symm = t := by
    rw [← hτ', Finset.image_image]
    simp
  apply Finset.card_bij (fun π _ => π.trans τ)
  · intro π hπ
    simp only [imageFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    rw [image_trans, hπ, hτ']
  · intro π₁ _ π₂ _ he
    ext x
    exact τ.injective (congrArg (fun e : Equiv.Perm α => e x) he)
  · intro π hπ
    refine ⟨π.trans τ.symm, ?_, ?_⟩
    · simp only [imageFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      rw [image_trans, hπ, hτinv]
    · ext x
      exact τ.apply_symm_apply (π x)

theorem image_mem_powersetCard (s : Finset α) (π : Equiv.Perm α) :
    s.image π ∈ (Finset.univ : Finset α).powersetCard s.card := by
  apply Finset.mem_powersetCard.mpr
  exact ⟨Finset.subset_univ _, Finset.card_image_iff.mpr π.injective.injOn⟩

/-- The labels occupying any fixed collection of positions in an actual uniform
permutation form a uniform fixed-size subset. The proof constructs equal fibers. -/
theorem permutation_image_mean (s : Finset α) (f : Finset α → ℝ) :
    (∑ π : Equiv.Perm α, f (s.image π)) / Fintype.card (Equiv.Perm α) =
      subsetMean Finset.univ s.card f := by
  have hs : s ∈ (Finset.univ : Finset α).powersetCard s.card := by simp
  have hmap : ((Finset.univ : Finset (Equiv.Perm α)) : Set (Equiv.Perm α)).MapsTo
      (fun π : Equiv.Perm α => s.image π) ((Finset.univ : Finset α).powersetCard s.card) :=
    fun π _ => image_mem_powersetCard s π
  have hcard : Fintype.card (Equiv.Perm α) =
      ((Finset.univ : Finset α).powersetCard s.card).card * (imageFiber s s).card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmap]
    calc
      _ = ∑ _t ∈ (Finset.univ : Finset α).powersetCard s.card, (imageFiber s s).card := by
        apply Finset.sum_congr rfl
        intro t ht
        exact imageFiber_card_eq s t s (Finset.mem_powersetCard.mp ht).2
      _ = _ := by simp
  have hsum : (∑ π : Equiv.Perm α, f (s.image π)) =
      ((imageFiber s s).card : ℝ) *
        ∑ t ∈ (Finset.univ : Finset α).powersetCard s.card, f t := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    calc
      _ = ∑ t ∈ (Finset.univ : Finset α).powersetCard s.card,
          ((imageFiber s s).card : ℝ)*f t := by
        apply Finset.sum_congr rfl
        intro t ht
        have he : ∀ (π : Equiv.Perm α), π ∈ (Finset.univ : Finset (Equiv.Perm α)).filter
            (fun π : Equiv.Perm α => s.image π = t) → f (s.image π) = f t := by
          intro π hπ
          rw [(Finset.mem_filter.mp hπ).2]
        rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
        change ((imageFiber s t).card : ℝ)*f t = _
        rw [imageFiber_card_eq s t s (Finset.mem_powersetCard.mp ht).2]
      _ = _ := by rw [Finset.mul_sum]
  have hpos : 0 < (imageFiber s s).card := by
    apply Finset.card_pos.mpr
    exact ⟨Equiv.refl α, by simp [imageFiber]⟩
  rw [hsum, hcard, Nat.cast_mul]
  unfold subsetMean
  have hz : ((imageFiber s s).card : ℝ) ≠ 0 := by positivity
  field_simp

theorem permutation_prefix_exp_le_product (s : Finset α)
    (hn : 0 < Fintype.card α) (r : α → ℝ) (hr : ∀ x, 0 ≤ r x)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ π : Equiv.Perm α, Real.exp (t*∑ x ∈ s.image π, r x)) /
      Fintype.card (Equiv.Perm α) ≤
      ∏ x, (1+((s.card:ℝ)/Fintype.card α)*(Real.exp (t*r x)-1)) := by
  rw [permutation_image_mean s (fun u => Real.exp (t*∑ x ∈ u, r x))]
  simpa using subset_exp_le_product Finset.univ s.card
    (by simpa using hn) (by simpa using Finset.card_le_card (Finset.subset_univ s))
    r (fun x _ => hr x) t ht

theorem exp_mass_chord {W t z : ℝ} (hW : 0 < W) (_ht : 0 ≤ t)
    (hz : 0 ≤ z) (hzW : z ≤ W) :
    Real.exp (t*z)-1 ≤ (z/W)*(Real.exp (t*W)-1) := by
  have hr0 : 0 ≤ z/W := div_nonneg hz hW.le
  have hr1 : z/W ≤ 1 := (div_le_one hW).mpr hzW
  have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (t*W))
    (sub_nonneg.mpr hr1) hr0 (by ring : (1-z/W)+(z/W)=1)
  have he : (1-z/W)*(0:ℝ)+(z/W)*(t*W) = t*z := by field_simp; ring
  simp only [smul_eq_mul, he, Real.exp_zero, mul_one] at hc
  linarith

/-- The exponential moment of root mass in fixed positions of an actual
uniform original-label permutation, with the correct original-edge weight cap. -/
theorem permutation_prefix_mgf (s : Finset α) (hn : 0 < Fintype.card α)
    (r : α → ℝ) {W t : ℝ} (hW : 0 < W) (ht : 0 ≤ t)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ W) :
    (∑ π : Equiv.Perm α, Real.exp (t*∑ x ∈ s.image π, r x)) /
      Fintype.card (Equiv.Perm α) ≤
      Real.exp (((s.card:ℝ)/Fintype.card α)*((∑ x, r x)/W)*(Real.exp (t*W)-1)) := by
  let a : ℝ := (s.card:ℝ)/Fintype.card α
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsum : (∑ x, a*(Real.exp (t*r x)-1)) ≤
      a*((∑ x, r x)/W)*(Real.exp (t*W)-1) := by
    calc
      _ ≤ ∑ x, a*((r x/W)*(Real.exp (t*W)-1)) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (exp_mass_chord hW ht (hr x).1 (hr x).2) ha
      _ = _ := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div]
        ring
  calc
    _ ≤ ∏ x, (1+a*(Real.exp (t*r x)-1)) :=
      permutation_prefix_exp_le_product s hn r (fun x => (hr x).1) t ht
    _ ≤ ∏ x, Real.exp (a*(Real.exp (t*r x)-1)) := by
      apply Finset.prod_le_prod
      · intro x _
        have he : 0 ≤ Real.exp (t*r x)-1 :=
          sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg ht (hr x).1))
        positivity
      · intro x _
        simpa [add_comm] using Real.add_one_le_exp (a*(Real.exp (t*r x)-1))
    _ = Real.exp (∑ x, a*(Real.exp (t*r x)-1)) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hsum

theorem permutation_prefix_chernoff (s : Finset α) (hn : 0 < Fintype.card α)
    (r : α → ℝ) {W t B : ℝ} (hW : 0 < W) (ht : 0 ≤ t)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ W) :
    ((Finset.univ.filter (fun π : Equiv.Perm α => B ≤ ∑ x ∈ s.image π, r x)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤
      Real.exp (-t*B + ((s.card:ℝ)/Fintype.card α)*((∑ x, r x)/W)*
        (Real.exp (t*W)-1)) := by
  have hp (π : Equiv.Perm α) :
      (if B ≤ ∑ x ∈ s.image π, r x then (1:ℝ) else 0) ≤
        Real.exp (-t*B)*Real.exp (t*∑ x ∈ s.image π, r x) := by
    split_ifs with hb
    · rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have h := mul_le_mul_of_nonneg_left hb ht
      linarith
    · positivity
  have hd : (0:ℝ) < Fintype.card (Equiv.Perm α) := by positivity
  have hs := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (s := Finset.univ) fun π _ => hp π) hd.le
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  rw [← Finset.mul_sum, mul_div_assoc] at hs
  calc
    _ ≤ Real.exp (-t*B)*
        ((∑ π : Equiv.Perm α, Real.exp (t*∑ x ∈ s.image π, r x)) /
          Fintype.card (Equiv.Perm α)) := hs
    _ ≤ Real.exp (-t*B)*Real.exp (((s.card:ℝ)/Fintype.card α)*
          ((∑ x, r x)/W)*(Real.exp (t*W)-1)) :=
      mul_le_mul_of_nonneg_left (permutation_prefix_mgf s hn r hW ht hr)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

end Permutation

/-- The sub-gamma exponential remainder on the range used by the finite phase.
It follows from a fourth-order Taylor bound already proved in mathlib. -/
theorem exp_remainder_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 - x ≤ x^2/(2*(1-x/3)) := by
  have ht := Real.exp_bound' hx hx1 (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have hd : 0 < 2*(1-x/3) := by linarith
  apply (le_div_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_right ht hd.le
  have h4 : 0 ≤ x^4 := pow_nonneg hx 4
  have h5 : 0 ≤ x^5 := pow_nonneg hx 5
  nlinarith

/-- Exact optimization of the sub-gamma bound. The modest mass assumption
ensures that only the Taylor interval [0,1] is needed. -/
theorem bernstein_parameter {W R L : ℝ} (hW : 0 < W) (hR : 0 < R)
    (hL : 0 < L) (hmass : 2*W*L ≤ R) :
    ∃ t : ℝ, 0 < t ∧ t*W ≤ 1 ∧
      -t*(Real.sqrt (2*W*R*L)+W*L/3) +
        W*R*t^2/(2*(1-t*W/3)) = -L := by
  let z := Real.sqrt (2*W*L/R)
  have hratio : 0 < 2*W*L/R := by positivity
  have hz : 0 < z := Real.sqrt_pos.mpr hratio
  have hsq : z^2 = 2*W*L/R := Real.sq_sqrt hratio.le
  have hz1 : z ≤ 1 := by
    have hh := (div_le_one hR).mpr hmass
    nlinarith
  have hrel : R*z^2 = 2*W*L := by rw [hsq]; field_simp
  have hroot : Real.sqrt (2*W*R*L) = R*z := by
    have h1 := Real.sq_sqrt (by positivity : 0 ≤ 2*W*R*L)
    have h2 : (R*z)^2 = 2*W*R*L := by nlinarith [congrArg (fun x : ℝ => R*x) hrel]
    have h3 : 0 ≤ Real.sqrt (2*W*R*L) := Real.sqrt_nonneg _
    have h4 : 0 < R*z := mul_pos hR hz
    nlinarith
  let d : ℝ := 1+z/3
  have hd : 0 < d := by dsimp [d]; positivity
  let t : ℝ := z/(W*d)
  have ht : 0 < t := by dsimp [t]; positivity
  have htw : t*W = z/d := by dsimp [t]; field_simp
  have htw1 : t*W ≤ 1 := by
    rw [htw]
    apply (div_le_one hd).mpr
    dsimp [d]
    linarith
  refine ⟨t, ht, htw1, ?_⟩
  have hden : 1-t*W/3 = 1/d := by
    rw [htw]
    dsimp [d]
    field_simp
    ring
  have hLeq : L = R*z^2/(2*W) := by
    apply (eq_div_iff (by positivity : 2*W ≠ 0)).mpr
    nlinarith [hrel]
  rw [hroot, hden, hLeq]
  dsimp [t, d]
  field_simp
  ring

section Tail
variable [Fintype α]

/-- Explicit finite root-prefix concentration with original-edge weight cap W.
The probability is the actual fraction of full permutations in the bad event. -/
theorem permutation_prefix_bernstein (s : Finset α) (hn : 0 < Fintype.card α)
    (r : α → ℝ) {W R L : ℝ} (hW : 0 < W) (hR : 0 < R) (hL : 0 < L)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ W) (hsum : ∑ x, r x = R)
    (hmass : 2*W*L ≤ R) :
    ((Finset.univ.filter (fun π : Equiv.Perm α =>
      ((s.card:ℝ)/Fintype.card α)*R + Real.sqrt (2*W*R*L)+W*L/3
        ≤ ∑ x ∈ s.image π, r x)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤ Real.exp (-L) := by
  obtain ⟨t, ht, htw, hopt⟩ := bernstein_parameter hW hR hL hmass
  let a : ℝ := (s.card:ℝ)/Fintype.card α
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hn : (0:ℝ) < Fintype.card α)).mpr
    exact_mod_cast Finset.card_le_card (Finset.subset_univ s)
  have he := exp_remainder_le (mul_nonneg ht.le hW.le) htw
  have hrem : 0 ≤ Real.exp (t*W)-1-t*W := by
    have h := Real.add_one_le_exp (t*W)
    linarith
  have haR : 0 ≤ R/W := div_nonneg hR.le hW.le
  have hreduce : a*(R/W)*(Real.exp (t*W)-1-t*W) ≤
      (R/W)*(t*W)^2/(2*(1-t*W/3)) := by
    calc
      _ ≤ (R/W)*(Real.exp (t*W)-1-t*W) := by
        have hh := mul_le_mul_of_nonneg_right ha1 (mul_nonneg haR hrem)
        nlinarith
      _ ≤ (R/W)*((t*W)^2/(2*(1-t*W/3))) :=
        mul_le_mul_of_nonneg_left he haR
      _ = _ := by ring
  have halg : (R/W)*(t*W)^2/(2*(1-t*W/3)) =
      W*R*t^2/(2*(1-t*W/3)) := by congr 1; field_simp
  rw [halg] at hreduce
  have hcancel : -t*(a*R + Real.sqrt (2*W*R*L)+W*L/3) +
      a*(R/W)*(Real.exp (t*W)-1) =
      -t*(Real.sqrt (2*W*R*L)+W*L/3) +
        a*(R/W)*(Real.exp (t*W)-1-t*W) := by field_simp; ring
  have htail := permutation_prefix_chernoff s hn r (B :=
    a*R+Real.sqrt (2*W*R*L)+W*L/3) hW ht.le hr
  rw [hsum] at htail
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  change -t*(a*R+Real.sqrt (2*W*R*L)+W*L/3) +
    a*(R/W)*(Real.exp (t*W)-1) ≤ -L
  rw [hcancel]
  linarith [hopt, hreduce]

/-- Simultaneous finite-prefix concentration; no independence between prefix
events is assumed. Taking I to be the set of phase positions gives the union
bound used in the high-probability phase proof. -/
theorem simultaneous_prefix_bernstein {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (s : ι → Finset α) (hn : 0 < Fintype.card α)
    (r : α → ℝ) {W R L : ℝ} (hW : 0 < W) (hR : 0 < R) (hL : 0 < L)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ W) (hsum : ∑ x, r x = R)
    (hmass : 2*W*L ≤ R) :
    ((I.biUnion (fun i => Finset.univ.filter (fun π : Equiv.Perm α =>
      (((s i).card:ℝ)/Fintype.card α)*R + Real.sqrt (2*W*R*L)+W*L/3
        ≤ ∑ x ∈ (s i).image π, r x))).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤ (I.card:ℝ)*Real.exp (-L) := by
  let bad : ι → Finset (Equiv.Perm α) := fun i => Finset.univ.filter
    (fun π : Equiv.Perm α =>
      (((s i).card:ℝ)/Fintype.card α)*R + Real.sqrt (2*W*R*L)+W*L/3
        ≤ ∑ x ∈ (s i).image π, r x)
  have hu : ((I.biUnion bad).card : ℝ) ≤ ∑ i ∈ I, ((bad i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  calc
    _ ≤ (∑ i ∈ I, ((bad i).card : ℝ)) / Fintype.card (Equiv.Perm α) :=
      div_le_div_of_nonneg_right hu (by positivity)
    _ = ∑ i ∈ I, ((bad i).card : ℝ)/Fintype.card (Equiv.Perm α) :=
      Finset.sum_div _ _ _
    _ ≤ ∑ _i ∈ I, Real.exp (-L) := by
      apply Finset.sum_le_sum
      intro i hi
      exact permutation_prefix_bernstein (s i) hn r hW hR hL hr hsum hmass
    _ = _ := by simp

end Tail

end RobustMatching.R7ProbabilityPrefix

#print axioms RobustMatching.R7ProbabilityPrefix.subset_probability_le
#print axioms RobustMatching.R7ProbabilityPrefix.subset_exp_le_product
#print axioms RobustMatching.R7ProbabilityPrefix.permutation_prefix_exp_le_product
#print axioms RobustMatching.R7ProbabilityPrefix.permutation_prefix_mgf
#print axioms RobustMatching.R7ProbabilityPrefix.permutation_prefix_chernoff
#print axioms RobustMatching.R7ProbabilityPrefix.exp_remainder_le
#print axioms RobustMatching.R7ProbabilityPrefix.permutation_prefix_bernstein
#print axioms RobustMatching.R7ProbabilityPrefix.simultaneous_prefix_bernstein
