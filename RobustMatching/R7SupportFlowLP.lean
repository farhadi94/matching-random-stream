import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact finite LP certificates and safe integer-bin tests. The numerical
96-bin certificate and its graph instantiation are not asserted by this file. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlow

theorem finite_linear_certificate
    {I E B : Type*} [Fintype I] [Fintype E] [Fintype B]
    (A : E → I → ℝ) (D : B → I → ℝ)
    (rhs : E → ℝ) (upper : B → ℝ) (cost x : I → ℝ)
    (ye : E → ℝ) (yb : B → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (he : ∀ e, (∑ i, A e i*x i)=rhs e)
    (hb : ∀ b, (∑ i, D b i*x i)≤upper b)
    (hy : ∀ b, yb b ≤ 0)
    (hc : ∀ i, (∑ e, ye e*A e i)+(∑ b, yb b*D b i)≤cost i) :
    (∑ e, ye e*rhs e)+(∑ b, yb b*upper b)≤∑ i, cost i*x i := by
  have heq : (∑ e, ye e*rhs e) = ∑ i, (∑ e, ye e*A e i)*x i := by
    simp_rw [← he, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hineq : (∑ b, yb b*upper b) ≤ ∑ i, (∑ b, yb b*D b i)*x i := by
    calc
      (∑ b, yb b*upper b) ≤ ∑ b, yb b*(∑ i, D b i*x i) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonpos_left (hb b) (hy b)
      _ = ∑ i, (∑ b, yb b*D b i)*x i := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
  calc
    (∑ e, ye e*rhs e)+(∑ b, yb b*upper b) ≤
      (∑ i, (∑ e, ye e*A e i)*x i)+(∑ i, (∑ b, yb b*D b i)*x i) := by
        rw [heq]
        exact add_le_add le_rfl hineq
    _ = ∑ i, ((∑ e, ye e*A e i)+(∑ b, yb b*D b i))*x i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, cost i*x i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hc i) (hx i)

/-- A small positive lambda does not add a new admissible integer bin pair. -/
theorem lower_pair_bin_safe {q i j : ℕ} {a b lam : ℝ}
    (hq : 0 < (q : ℝ))
    (ha : a*q < (i : ℝ)+1) (hb : b*q < (j : ℝ)+1)
    (hlam : lam*q < 1) (hsum : 1-lam ≤ a+b) :
    q ≤ i+j+2 := by
  by_contra hn
  have hn' : i+j+3 ≤ q := by omega
  have hreal : (i : ℝ)+(j : ℝ)+3 ≤ q := by exact_mod_cast hn'
  have hm := mul_le_mul_of_nonneg_right hsum hq.le
  nlinarith

theorem upper_pair_bin_safe {q i j : ℕ} {a b : ℝ}
    (hq : 0 ≤ (q : ℝ))
    (ha : (i : ℝ) ≤ a*q) (hb : (j : ℝ) ≤ b*q)
    (hsum : a+b ≤ 1) :
    i+j ≤ q := by
  have hm := mul_le_mul_of_nonneg_right hsum hq
  have hr : (i : ℝ)+(j : ℝ) ≤ q := by nlinarith
  exact_mod_cast hr

/-- A semantic column type may include impossible class pairs. Their
primal coordinates are zero, so only admissible columns need a certificate. -/
theorem finite_linear_certificate_supported
    {I E B : Type*} [Fintype I] [Fintype E] [Fintype B]
    (A : E → I → ℝ) (D : B → I → ℝ)
    (rhs : E → ℝ) (upper : B → ℝ) (cost x : I → ℝ)
    (ye : E → ℝ) (yb : B → ℝ) (allowed : I → Prop)
    (hx : ∀ i, 0 ≤ x i)
    (hsupport : ∀ i, ¬allowed i → x i=0)
    (he : ∀ e, (∑ i, A e i*x i)=rhs e)
    (hb : ∀ b, (∑ i, D b i*x i)≤upper b)
    (hy : ∀ b, yb b ≤ 0)
    (hc : ∀ i, allowed i →
      (∑ e, ye e*A e i)+(∑ b, yb b*D b i)≤cost i) :
    (∑ e, ye e*rhs e)+(∑ b, yb b*upper b)≤∑ i, cost i*x i := by
  classical
  let cost' : I → ℝ := fun i => if allowed i then cost i else
    (∑ e, ye e*A e i)+(∑ b, yb b*D b i)
  have hc' : ∀ i,
      (∑ e, ye e*A e i)+(∑ b, yb b*D b i)≤cost' i := by
    intro i
    by_cases hi : allowed i
    · simpa [cost',hi] using hc i hi
    · simp [cost',hi]
  calc
    (∑ e, ye e*rhs e)+(∑ b, yb b*upper b) ≤ ∑ i, cost' i*x i :=
      finite_linear_certificate A D rhs upper cost' x ye yb hx he hb hy hc'
    _ = ∑ i, cost i*x i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : allowed i
      · simp [cost',hi]
      · simp [hsupport i hi]

end RobustMatching.R7SupportFlow

#print axioms RobustMatching.R7SupportFlow.finite_linear_certificate
#print axioms RobustMatching.R7SupportFlow.lower_pair_bin_safe
#print axioms RobustMatching.R7SupportFlow.upper_pair_bin_safe
#print axioms RobustMatching.R7SupportFlow.finite_linear_certificate_supported
