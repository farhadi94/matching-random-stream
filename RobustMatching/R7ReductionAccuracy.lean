import RobustMatching.R7ReductionWindows
import RobustMatching.R7ReductionFailure

/-! Explicit finite error accounting for the shifted compiler. -/
noncomputable section
namespace RobustMatching.R7ReductionAccuracy

theorem product_loss {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1-x-y-z ≤ (1-x)*(1-y)*(1-z) := by
  have hxy : 0 ≤ x*y*(1-z) := mul_nonneg (mul_nonneg hx hy) (by linarith)
  have hzx : 0 ≤ z*(x+y) := mul_nonneg hz (add_nonneg hx hy)
  nlinarith

theorem total_accuracy {alpha eps x y z c : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hz1 : z ≤ 1) (hc : 0 ≤ c)
    (hbudget : x+y+z+c ≤ eps) :
    alpha-eps ≤ alpha*(1-x)*(1-y)*(1-z)/(1+c) := by
  have hp := product_loss hx hy hz hz1
  have hpalpha := mul_le_mul_of_nonneg_left hp ha
  have hsum : 0 ≤ x+y+z+c := by positivity
  have hscale : alpha*(x+y+z+c) ≤ x+y+z+c := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-alpha) hsum]
  have hstart : alpha-eps ≤ alpha*(1-x-y-z-c) := by nlinarith
  have hcross : 0 ≤ alpha*c*(x+y+z+c) := by positivity
  have hprod : alpha*(1-x-y-z-c)*(1+c) ≤ alpha*(1-x)*(1-y)*(1-z) := by
    nlinarith
  apply (le_div_iff₀ (by linarith : 0 < 1+c)).mpr
  exact (mul_le_mul_of_nonneg_right hstart (by linarith)).trans hprod

theorem planned_budget {alpha theta c z : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hc : 0 ≤ c) (hct : c ≤ theta/8) (hz : 0 ≤ z) (hzt : z ≤ theta/8) :
    alpha-theta ≤ alpha*(1-theta/4)*(1-theta/8)*(1-z)/(1+c) := by
  apply total_accuracy ha ha1 (by positivity) (by positivity) hz (by linarith) hc
  linarith

end RobustMatching.R7ReductionAccuracy

#print axioms RobustMatching.R7ReductionAccuracy.total_accuracy
#print axioms RobustMatching.R7ReductionAccuracy.planned_budget
