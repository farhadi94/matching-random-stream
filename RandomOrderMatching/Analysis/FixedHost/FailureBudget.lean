import RandomOrderMatching.Analysis.FixedHost.ClockTransfer
import RandomOrderMatching.Certificates.DegreeProfile.Certificate

noncomputable section
namespace RandomOrderMatching.Analysis.FixedHost
open RandomOrderMatching.Analysis.Repair.Probability RandomOrderMatching.Analysis.Repair.Typed RandomOrderMatching.Probability.ClockCoupling MeasureTheory

theorem suffix_bracket_budget {n : ℕ} {N θ L : ℝ}
    (hN : 1≤N) (hθ : 0≤θ) (_hL : 0≤L)
    (hscale : Real.exp (-L)≤θ/N)
    (hlength : 70000000000000000000000000000*L≤(n:ℝ)) :
    2*Real.exp (-(n:ℝ)/8000000000000)≤2*θ := by
  have hn : 0<N := by linarith
  have he : -(n:ℝ)/8000000000000≤-L := by nlinarith
  have hs : θ/N≤θ := (div_le_iff₀ hn).mpr (by nlinarith)
  exact mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr he).trans (hscale.trans hs)) (by norm_num)

theorem suffix_length_short_threshold {n : ℕ} {L : ℝ} (hL : 1≤L)
    (hlength : 70000000000000000000000000000*L≤(n:ℝ)) : 10000000≤n := by
  have hn : (10000000:ℝ)≤n := by nlinarith
  exact_mod_cast hn

theorem target_below_base_branch :
    (RandomOrderMatching.Certificates.DegreeProfile.Concrete.target:ℝ)-1/10000000<714/1000 := by
  norm_num [RandomOrderMatching.Certificates.DegreeProfile.Concrete.target]

end RandomOrderMatching.Analysis.FixedHost
