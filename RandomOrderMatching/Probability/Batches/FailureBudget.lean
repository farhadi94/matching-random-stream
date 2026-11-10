import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! Final finite logarithmic failure budget. This is numerical probability
bookkeeping, separate from the actual-clock tail theorem and graph witnesses. -/

namespace RandomOrderMatching

theorem log_le_logb_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ Real.logb 2 x := by
  have hx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2' : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  rw [Real.logb, le_div_iff₀ h2]
  nlinarith

theorem log_le_ceil_logb_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (⌈Real.logb 2 x⌉₊ : ℝ) :=
  (log_le_logb_two hx).trans (Nat.le_ceil _)

theorem batch_failure_base
    {n δ Lstar : ℝ} (hn : 2 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hL : Real.log (100 * n / δ) ≤ Lstar) :
    0 ≤ Lstar ∧ Real.exp (-Lstar) ≤ δ / (100 * n) := by
  have hn0 : 0 < n := by linarith
  have hx : 1 ≤ 100 * n / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hx0 : 0 < 100 * n / δ := by positivity
  constructor
  · exact (Real.log_nonneg hx).trans hL
  · calc
      Real.exp (-Lstar) ≤ Real.exp (-Real.log (100 * n / δ)) :=
        Real.exp_le_exp.mpr (neg_le_neg hL)
      _ = δ / (100 * n) := by
        rw [Real.exp_neg, Real.exp_log hx0]
        field_simp

/-- Root, center, four aggregate/late events, and the two-sided cutoff bracket
fit in 7δ/100. The three event families need only their individual bounds. -/
theorem batch_failure_seven_percent
    {n δ Lstar r b q : ℝ}
    (hn : 2 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hL : Real.log (100 * n / δ) ≤ Lstar)
    (_hr : 0 ≤ r) (_hb : 0 ≤ b) (hrn : 2 * r ≤ n) (hbn : b ≤ n)
    (hq : (14 / 100 : ℝ) * 10 ^ 18 * Lstar ≤ q) :
    2 * r * Real.exp (-200 * Lstar) + b * Real.exp (-2 * Lstar)
      + 4 * (δ / 100) +
      2 * Real.exp (-2 * (1 / (4 * 10 ^ 6) : ℝ) ^ 2 * q) ≤
      7 * δ / 100 := by
  obtain ⟨hL0, hbase⟩ := batch_failure_base hn hδ hδ1 hL
  have hn0 : 0 < n := by linarith
  have hnbase : n * Real.exp (-Lstar) ≤ δ / 100 := by
    calc
      n * Real.exp (-Lstar) ≤ n * (δ / (100 * n)) :=
        mul_le_mul_of_nonneg_left hbase hn0.le
      _ = δ / 100 := by field_simp
  have hroot : 2 * r * Real.exp (-200 * Lstar) ≤ δ / 100 := by
    calc
      _ ≤ n * Real.exp (-Lstar) := mul_le_mul hrn
        (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le hn0.le
      _ ≤ _ := hnbase
  have hcenter : b * Real.exp (-2 * Lstar) ≤ δ / 100 := by
    calc
      _ ≤ n * Real.exp (-Lstar) := mul_le_mul hbn
        (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le hn0.le
      _ ≤ _ := hnbase
  have hexponent : -2 * (1 / (4 * 10 ^ 6) : ℝ) ^ 2 * q ≤ -Lstar := by
    norm_num at hq ⊢
    linarith
  have hbracket : 2 * Real.exp (-2 * (1 / (4 * 10 ^ 6) : ℝ) ^ 2 * q)
      ≤ δ / 100 := by
    calc
      _ ≤ n * Real.exp (-Lstar) := mul_le_mul hn
        (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le hn0.le
      _ ≤ _ := hnbase
  linarith

/-- The actual specified natural ceiling supplies the logarithmic hypothesis. -/
theorem batch_failure_seven_percent_ceil
    {n δ r b q : ℝ}
    (hn : 2 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hrn : 2 * r ≤ n) (hbn : b ≤ n)
    (hq : (14 / 100 : ℝ) * 10 ^ 18 * (⌈Real.logb 2 (100 * n / δ)⌉₊ : ℝ) ≤ q) :
    2 * r * Real.exp (-200 * (⌈Real.logb 2 (100 * n / δ)⌉₊ : ℝ))
      + b * Real.exp (-2 * (⌈Real.logb 2 (100 * n / δ)⌉₊ : ℝ))
      + 4 * (δ / 100) +
      2 * Real.exp (-2 * (1 / (4 * 10 ^ 6) : ℝ) ^ 2 * q) ≤
      7 * δ / 100 := by
  apply batch_failure_seven_percent hn hδ hδ1 _ hr hb hrn hbn hq
  apply log_le_ceil_logb_two
  apply (le_div_iff₀ hδ).mpr
  nlinarith

end RandomOrderMatching

#print axioms RandomOrderMatching.log_le_ceil_logb_two
#print axioms RandomOrderMatching.batch_failure_seven_percent_ceil
