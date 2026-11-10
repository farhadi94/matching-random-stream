import RandomOrderMatching.Weights.Windows.Approximation

noncomputable section
namespace RandomOrderMatching.Weights.Windows

/-- Exact rational implementation of the advertised parameter choices. -/
def planned (theta : ℚ) (ht : 0 < theta) (ht1 : theta ≤ 1) : Parameters where
  B := (⌈32/theta⌉₊ : ℚ)
  eta := theta/4
  k := ⌈8/theta⌉₊
  base_gt_one := by
    have hc := Nat.le_ceil (32/theta)
    have h32 : (32:ℚ) ≤ theta*(⌈32/theta⌉₊:ℚ) := by
      have h := (div_le_iff₀ ht).mp hc
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right ht1 (show (0:ℚ) ≤ ⌈32/theta⌉₊ by positivity)
    nlinarith
  eta_pos := by positivity
  eta_le_one := by linarith
  width_pos := Nat.ceil_pos.mpr (by positivity)

namespace Parameters
theorem greedyLoss_le_four_div (p : Parameters) (hB : 2 ≤ (p.B:ℝ)) :
    p.greedyLoss ≤ 4/(p.B:ℝ) := by
  have hB0 : 0 < (p.B:ℝ) := lt_trans zero_lt_one p.base_real
  have hr : (p.B:ℝ)^(-((p.k+1:ℕ):ℤ)) ≤ (p.B:ℝ)^(-1:ℤ) :=
    zpow_le_zpow_right₀ p.base_real.le (by omega)
  have hinv : (p.B:ℝ)^(-1:ℤ) ≤ 1/2 := by
    simp only [zpow_neg_one]
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hB
  have hr2 := hr.trans hinv
  have hden : 0 < (p.B:ℝ)*(1-(p.B:ℝ)^(-((p.k+1:ℕ):ℤ))) :=
    mul_pos hB0 (by linarith)
  unfold greedyLoss
  apply (div_le_iff₀ hden).mpr
  have heq : 4/(p.B:ℝ)*((p.B:ℝ)*(1-(p.B:ℝ)^(-((p.k+1:ℕ):ℤ)))) =
      4*(1-(p.B:ℝ)^(-((p.k+1:ℕ):ℤ))) := by field_simp
  rw [heq]
  linarith
end Parameters

theorem planned_accuracy (theta : ℚ) (ht : 0 < theta) (ht1 : theta ≤ 1)
    {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    alpha-(theta:ℝ) ≤ (planned theta ht ht1).ratio alpha := by
  let p := planned theta ht ht1
  have htR : 0 < (theta:ℝ) := by exact_mod_cast ht
  have hBceil : (32:ℝ)/(theta:ℝ) ≤ (p.B:ℝ) := by
    have hh := Nat.le_ceil (32/theta)
    change (32:ℝ)/(theta:ℝ) ≤ ((⌈32/theta⌉₊:ℚ):ℝ)
    exact_mod_cast hh
  have hkceil : (8:ℝ)/(theta:ℝ) ≤ (p.k:ℝ) := by
    exact_mod_cast (Nat.le_ceil (8/theta))
  have hBt : 32 ≤ (p.B:ℝ)*(theta:ℝ) := (div_le_iff₀ htR).mp hBceil
  have hkt : 8 ≤ (p.k:ℝ)*(theta:ℝ) := (div_le_iff₀ htR).mp hkceil
  have htheta1 : (theta:ℝ) ≤ 1 := by exact_mod_cast ht1
  have hB0 : 0 < (p.B:ℝ) := lt_trans zero_lt_one p.base_real
  have hB2 : 2 ≤ (p.B:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left htheta1 hB0.le
    nlinarith
  have hC := p.greedyLoss_le_four_div hB2
  have hCtheta : p.greedyLoss ≤ (theta:ℝ)/8 := hC.trans (by
    apply (div_le_iff₀ hB0).mpr
    nlinarith)
  have hdrop : 1/(p.k+1:ℝ) ≤ (theta:ℝ)/8 := by
    apply (div_le_iff₀ (by positivity : 0 < (p.k+1:ℝ))).mpr
    nlinarith
  apply p.ratio_accuracy ha ha1
  have heta : (p.eta:ℝ) = (theta:ℝ)/4 := by simp [p, planned]
  rw [heta]
  linarith

end RandomOrderMatching.Weights.Windows
