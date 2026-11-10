import RobustMatching.R7ReductionCertificateColumns
import RobustMatching.R7ReductionCertificateGrid
import RobustMatching.R7SupportFlowLP
set_option maxHeartbeats 0
open scoped BigOperators
namespace RobustMatching.R7ReductionCertificate.Concrete
open RobustMatching.R7ReductionCertificate

theorem eq_objective {q} (y : EqRow q → ℚ) : (∑ r,y r*rhsEq r) = y .normalization := by
  classical
  have he (r : EqRow q) : rhsEq r = if r = .normalization then 1 else 0 := by
    cases r <;> simp [rhsEq,reduceCtorEq]
  simp_rw [he,mul_ite,mul_one,mul_zero]
  simp

theorem le_objective {q} (d : ProfileData q) (y : LeRow q → ℚ) :
    (∑ r,y r*rhsLe d r) = y .baseOne+y .valueOne+y .mass*d.massBound := by
  classical
  have he (r : LeRow q) : rhsLe d r =
      (if r = .baseOne then 1 else 0)+(if r = .valueOne then 1 else 0)+
      (if r = .mass then (d.massBound:ℚ) else 0) := by
    cases r <;> simp [rhsLe,reduceCtorEq]
  simp_rw [he,mul_add,mul_ite,mul_one,mul_zero]
  simp [Finset.sum_add_distrib]

def target : ℚ := 2896371675910694789/4062500000000000000

theorem objective_exact :
    (∑ r,dualEq r*rhsEq r)+(∑ r,dualLe r*rhsLe data r) = target := by
  rw [eq_objective,le_objective]
  norm_num [dualEq,dualLe,dualEqNumerator,dualLeNumerator,dualDenominator,data,target]

theorem dualLe_nonpositive (r : LeRow 152) : dualLe r ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · exact_mod_cast dual_le_signs r
  · norm_num [dualDenominator]

/-- Concrete exact certificate: actual semantic matrix feasibility implies
the fixed numerical lower bound. No column bound or dual validity is an
assumption; both are established by the kernel-checked certificate. -/
theorem exact_profile_certificate (x : Column 152 → ℝ)
    (hx : ∀ c,0 ≤ x c)
    (hsupport : ∀ c,¬columnAllowed data c → x c=0)
    (he : ∀ r,(∑ c,(coeffEq r c:ℝ)*x c)=(rhsEq r:ℝ))
    (hl : ∀ r,(∑ c,(coeffLe data r c:ℝ)*x c)≤(rhsLe data r:ℝ)) :
    (target:ℝ) ≤ x .value := by
  classical
  have hy (r : LeRow 152) : (dualLe r:ℝ) ≤ 0 := by
    exact_mod_cast dualLe_nonpositive r
  have hc (c : Column 152) (ha : columnAllowed data c) :
      (∑ r,(dualEq r:ℝ)*(coeffEq r c:ℝ))+
      (∑ r,(dualLe r:ℝ)*(coeffLe data r c:ℝ)) ≤ (cost c:ℝ) := by
    exact_mod_cast dense_rational_columns c ha
  have hb := RobustMatching.R7SupportFlow.finite_linear_certificate_supported
    (fun r c => (coeffEq r c:ℝ)) (fun r c => (coeffLe data r c:ℝ))
    (fun r => (rhsEq r:ℝ)) (fun r => (rhsLe data r:ℝ))
    (fun c => (cost c:ℝ)) x (fun r => (dualEq r:ℝ)) (fun r => (dualLe r:ℝ))
    (columnAllowed data) hx hsupport he hl hy hc
  have ho : (∑ r,(dualEq r:ℝ)*(rhsEq r:ℝ))+
      (∑ r,(dualLe r:ℝ)*(rhsLe data r:ℝ)) = (target:ℝ) := by
    exact_mod_cast objective_exact
  rw [ho] at hb
  have hv : (∑ c,(cost c:ℝ)*x c) = x .value := by
    have he (c : Column 152) : cost c = if c = .value then 1 else 0 := by
      cases c <;> simp [cost,reduceCtorEq]
    simp_rw [he]
    simp only [apply_ite, Rat.cast_one, Rat.cast_zero, ite_mul, one_mul, zero_mul]
    simp
  simpa only [hv] using hb

theorem post_error_ratio :
    (target-1/10000000)*(1-2/100000000) > 71295/100000 := by
  norm_num [target]

end RobustMatching.R7ReductionCertificate.Concrete
#print axioms RobustMatching.R7ReductionCertificate.Concrete.exact_profile_certificate
#print axioms RobustMatching.R7ReductionCertificate.Concrete.post_error_ratio
