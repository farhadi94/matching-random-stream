import RobustMatching.R8RepairProbabilityCounts

/-! Exact parameter arithmetic for the final finite probability reserve. -/
noncomputable section
open MeasureTheory
namespace RobustMatching.R8RepairProbability

def epsilon : ℝ := 1/1000000000000

lemma epsilon_pos : 0<epsilon := by norm_num [epsilon]

lemma beta_exponent {β κ L : ℝ} (hk : 0<κ)
    (hb : 10^30*κ*L/2≤β) : 125*L≤epsilon^2*β/(4000*κ) := by
  apply (le_div_iff₀ (by positivity : 0<4000*κ)).mpr
  norm_num [epsilon] at *
  nlinarith

lemma reserve_sqrt {β κ μ L : ℝ} (hk : 0≤κ) (hL : 0≤L) (hμ : 0≤μ)
    (hb : 10^30*κ*L/2≤β) (hm : (49:ℝ)/100*β≤μ) :
    Real.sqrt (κ*μ*L)≤μ/10000000000 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hsmall : κ*L≤μ/100000000000000000000 := by
      nlinarith [mul_nonneg hk hL]
    have hh := mul_le_mul_of_nonneg_right hsmall hμ
    nlinarith

/-- This deliberately proves the larger written reserve, before even using
the factor one-half in the structural transfer. -/
theorem finite_error_reserve {β κ μ L : ℝ} (hk : 0≤κ) (hL : 0≤L) (hμ : 0<μ)
    (hb : 10^30*κ*L/2≤β) (hm : (49:ℝ)/100*β≤μ) :
    2000*epsilon*μ+40*Real.sqrt (κ*μ*L)<μ/10000000 := by
  have hs := reserve_sqrt hk hL (le_of_lt hμ) hb hm
  norm_num [epsilon] at *
  linarith

lemma aggregate_sqrt_exponent {κ μ L : ℝ} (hk : 0<κ) (hμ : 0<μ) (hL : 0≤L) :
    -2*(Real.sqrt (κ*μ*L))^2/(κ*μ)= -2*L := by
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- The complete local family costs at most four theta once N dominates
mu and exp(-L) is at most theta/N. The extra factor exp(-L) absorbs the
conservative count eight mu. -/
lemma local_union_numeric {μ N θ L : ℝ} (hμ : 0≤μ) (hN : 0<N)
    (hμN : μ≤N) (hθ : 0≤θ) (hθsmall : θ/N≤1/2)
    (hL : 0≤L) (hscale : Real.exp (-L)≤θ/N) :
    8*μ*Real.exp (-125*L)≤4*θ := by
  have he : Real.exp (-125*L)≤(Real.exp (-L))^2 := by
    rw [pow_two,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hp : 0≤Real.exp (-L) := le_of_lt (Real.exp_pos _)
  have hhalf : Real.exp (-L)≤1/2 := hscale.trans hθsmall
  have h1 : Real.exp (-125*L)≤(1/2)*(θ/N) := by
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0≤8*μ)
  have h3 : μ*(θ/N)≤θ := by
    have hh := mul_le_mul_of_nonneg_right hμN (div_nonneg hθ (le_of_lt hN))
    have heq : N*(θ/N)=θ := by field_simp
    rw [heq] at hh
    exact hh
  nlinarith

lemma aggregate_union_numeric {θ L : ℝ} (hθ : 0≤θ) (hθsmall : θ≤1/5)
    (hscale : Real.exp (-L)≤θ) : 5*Real.exp (-2*L)≤θ := by
  have heq : Real.exp (-2*L)=(Real.exp (-L))^2 := by rw [pow_two,←Real.exp_add];congr 1;ring
  rw [heq]
  have hp := Real.exp_pos (-L)
  nlinarith

end RobustMatching.R8RepairProbability
