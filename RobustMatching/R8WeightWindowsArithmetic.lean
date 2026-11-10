import RobustMatching.R7ReductionWindows
import RobustMatching.R7ReductionActive
import RobustMatching.R7ReductionFailure
import RobustMatching.R3Precision

/-! Actual half-open rational windows and their exact integer normalization.
The exponent is specified by its unique geometric interval; all membership
and normalization comparisons are rational, including boundary weights. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8WeightWindows
open RobustMatching.R7ReductionWindows

structure Parameters where
  B : ℚ
  eta : ℚ
  k : ℕ
  base_gt_one : 1 < B
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  width_pos : 0 < k

namespace Parameters
variable (p : Parameters)

def lower (t : ℤ) : ℚ := p.B ^ t
def upper (t : ℤ) : ℚ := p.B ^ (t + (p.k : ℤ))
def contains (t : ℤ) (w : ℚ) : Prop := p.lower t ≤ w ∧ w < p.upper t
def normalized (t : ℤ) (w : ℚ) : ℕ := ⌊w / (p.eta * p.lower t)⌋₊
def integerRange : ℕ := ⌈p.B ^ p.k / p.eta⌉₊

theorem base_real : 1 < (p.B : ℝ) := by exact_mod_cast p.base_gt_one
theorem eta_real_pos : 0 < (p.eta : ℝ) := by exact_mod_cast p.eta_pos
theorem lower_pos (t : ℤ) : 0 < p.lower t := zpow_pos (by linarith [p.base_gt_one]) _

def exponent (w : ℚ) : ℤ :=
  if hw : 0 < w then
    Classical.choose (exponent_exists p.base_real (by exact_mod_cast hw : 0 < (w : ℝ)))
  else 0

theorem exponent_spec (w : ℚ) (hw : 0 < w) :
    p.lower (p.exponent w) ≤ w ∧ w < p.lower (p.exponent w + 1) := by
  have h := Classical.choose_spec
    (exponent_exists p.base_real (by exact_mod_cast hw : 0 < (w : ℝ)))
  simp only [exponent, dif_pos hw]
  unfold lower
  exact_mod_cast h

def windows (w : ℚ) : Finset ℤ :=
  if 0 < w then Finset.Ioc (p.exponent w - (p.k : ℤ)) (p.exponent w) else ∅

theorem mem_windows {w : ℚ} (hw : 0 < w) (t : ℤ) :
    t ∈ p.windows w ↔ p.contains t w := by
  have hs := p.exponent_spec w hw
  have hr : (p.B : ℝ) ^ p.exponent w ≤ (w : ℝ) ∧
      (w : ℝ) < (p.B : ℝ) ^ (p.exponent w + 1) := by
    exact_mod_cast hs
  rw [windows, if_pos hw, Finset.mem_Ioc]
  have hh := membership_iff p.base_real (p.exponent w) t p.k hr
  unfold contains lower upper
  exact (by exact_mod_cast hh.symm)

theorem windows_card (w : ℚ) (hw : 0 < w) : (p.windows w).card = p.k := by
  simp [windows, hw]

theorem normalized_real (t : ℤ) (w : ℚ) :
    p.normalized t w = ⌊(w : ℝ) / ((p.eta : ℝ) * (p.B : ℝ)^t)⌋₊ := by
  unfold normalized lower
  rw [← Int.floor_toNat, ← Int.floor_toNat, ← Rat.cast_zpow,
    ← Rat.cast_mul, ← Rat.cast_div, Rat.floor_cast]

theorem normalized_range {t : ℤ} {w : ℚ} (hw : p.contains t w) :
    1 ≤ p.normalized t w ∧ p.normalized t w ≤ p.integerRange := by
  have hL := p.lower_pos t
  have hq := mul_pos p.eta_pos hL
  have hlo : 1 ≤ w / (p.eta * p.lower t) := by
    apply (le_div_iff₀ hq).mpr
    have := mul_le_mul_of_nonneg_right p.eta_le_one hL.le
    nlinarith [hw.1]
  have hup : w / (p.eta * p.lower t) < p.B ^ p.k / p.eta := by
    apply (div_lt_div_iff₀ hq p.eta_pos).mpr
    have heq : p.upper t = p.lower t * p.B ^ p.k := by
      simp [upper, lower, zpow_add₀ (ne_of_gt (lt_trans zero_lt_one p.base_gt_one))]
    have := mul_lt_mul_of_pos_right hw.2 p.eta_pos
    rw [heq] at this
    nlinarith
  exact ⟨Nat.floor_pos.mpr hlo,
    (Nat.floor_mono hup.le).trans (Nat.floor_le_ceil _)⟩

theorem normalized_rounding (t : ℤ) (w : ℚ) :
    ((p.eta : ℝ) * (p.B : ℝ)^t) * (p.normalized t w : ℝ) =
      RobustMatching.R3Precision.rounded ((p.eta : ℝ) * (p.B : ℝ)^t) (w : ℝ) := by
  rw [normalized_real]
  rfl

end Parameters
end RobustMatching.R8WeightWindows
