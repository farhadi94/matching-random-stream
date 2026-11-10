import RobustMatching.R8WeightWindowsState

noncomputable section
namespace RobustMatching.R8WeightWindows.Parameters

def liveExponent (p : Parameters) (n : ℕ) : ℕ :=
  ⌈Real.logb (p.B:ℝ) ((n:ℝ)/(p.eta:ℝ))⌉₊

theorem liveExponent_spec (p : Parameters) (n : ℕ) (hn : 0 < n) :
    (p.B:ℝ)^(-(p.liveExponent n:ℤ)) ≤ (p.eta:ℝ)/n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hh := (Real.logb_le_iff_le_rpow p.base_real
    (div_pos hnR p.eta_real_pos)).mp
    (Nat.le_ceil (Real.logb (p.B:ℝ) ((n:ℝ)/(p.eta:ℝ))))
  rw [Real.rpow_natCast] at hh
  have hinv := one_div_le_one_div_of_le (div_pos hnR p.eta_real_pos) hh
  simpa [liveExponent,zpow_neg,zpow_natCast,one_div_div] using hinv

theorem exact_dictionary_count {V : Type*} [DecidableEq V]
    (p : Parameters) (w : RobustMatching.R2Cut.Edge V → ℚ)
    (n : ℕ) (hn : 0 < n) (stream : ℕ → RobustMatching.R2Cut.Edge V)
    (hw : ∀ e,0 < w e) (t : ℕ) :
    (p.dictionary w n stream t).card ≤ p.k+p.liveExponent n+1 :=
  p.dictionary_count w n stream hw _ (p.liveExponent_spec n hn) t

end RobustMatching.R8WeightWindows.Parameters
