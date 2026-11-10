import RobustMatching.R8StreamingWrapperUnion
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R8WeightWindows
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 800000

/-- Positive integer rounding of a binary logarithm. All confidence choices
are fixed from the vertex universe, bounded range and requested failure rate. -/
def ceilLogTwo (x : ℝ) : ℕ := max 1 ⌈Real.logb 2 x⌉₊

theorem ceilLogTwo_pos (x : ℝ) : 0 < ceilLogTwo x :=
  lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

theorem log_le_ceilLogTwo {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ (ceilLogTwo x:ℝ) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo1 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1 <;> norm_num
  have hx0 := Real.log_nonneg hx
  have hh : Real.log x ≤ Real.logb 2 x := by
    unfold Real.logb
    apply (le_div_iff₀ htwo).mpr
    exact mul_le_of_le_one_right hx0 htwo1
  exact hh.trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _)))

def confidenceVertices (n W : ℕ) : ℕ := max 2 (n*W)
def confidenceLog (n W : ℕ) (delta : ℝ) : ℕ :=
  ceilLogTwo (100*(confidenceVertices n W:ℝ)/delta)
def prefixLog (delta : ℝ) : ℕ := ceilLogTwo (3/delta)
def capLog (n W Q : ℕ) (delta : ℝ) : ℕ := ceilLogTwo (3*(Q:ℝ)/delta)

theorem confidenceLog_pos (n W : ℕ) (delta : ℝ) : 0 < confidenceLog n W delta :=
  ceilLogTwo_pos _

theorem confidenceLog_spec (n W : ℕ) {delta : ℝ} (hd : 0 < delta) (hd1 : delta < 1) :
    Real.log (100*(confidenceVertices n W:ℝ)/delta) ≤ (confidenceLog n W delta:ℝ) := by
  apply log_le_ceilLogTwo
  apply (le_div_iff₀ hd).mpr
  have hn : (2:ℝ) ≤ confidenceVertices n W := by exact_mod_cast le_max_left 2 (n*W)
  nlinarith

theorem prefixLog_spec {delta : ℝ} (hd : 0 < delta) (hd1 : delta < 1) :
    Real.log (3/delta) ≤ (prefixLog delta:ℝ) := by
  apply log_le_ceilLogTwo
  apply (le_div_iff₀ hd).mpr
  linarith

theorem capLog_spec (n W Q : ℕ) (hQ : 0 < Q) {delta : ℝ}
    (hd : 0 < delta) (hd1 : delta < 1) :
    Real.log (3*(Q:ℝ)/delta) ≤ (capLog n W Q delta:ℝ) := by
  apply log_le_ceilLogTwo
  apply (le_div_iff₀ hd).mpr
  have hqr : (1:ℝ) ≤ Q := Nat.one_le_cast.mpr hQ
  nlinarith

theorem confidence_budget_thirds {Q LU L0 delta : ℝ}
    (hQ : 0 < Q) (hd : 0 < delta)
    (h0 : Real.log (3/delta) ≤ L0) (hu : Real.log (3*Q/delta) ≤ LU) :
    Q*Real.exp (-LU)+Real.exp (-L0)+7*delta/100 ≤ delta := by
  have hzero := confidence_exp_bound (show 0 < delta/3 by positivity)
    (by convert h0 using 1 <;> congr 1 <;> field_simp : Real.log (1/(delta/3)) ≤ L0)
  have hupper := confidence_exp_bound (show 0 < delta/(3*Q) by positivity)
    (by convert hu using 1 <;> congr 1 <;> field_simp : Real.log (1/(delta/(3*Q))) ≤ LU)
  have hh := mul_le_mul_of_nonneg_left hupper hQ.le
  have he : Q*(delta/(3*Q))=delta/3 := by field_simp
  rw [he] at hh
  linarith

theorem actual_confidence_budget (n W Q : ℕ) (hQ : 0 < Q)
    {delta : ℝ} (hd : 0 < delta) (hd1 : delta < 1) :
    (Q:ℝ)*Real.exp (-(capLog n W Q delta:ℝ))+
      Real.exp (-(prefixLog delta:ℝ))+7*delta/100 ≤ delta :=
  confidence_budget_thirds (Nat.cast_pos.mpr hQ) hd (prefixLog_spec hd hd1)
    (capLog_spec n W Q hQ hd hd1)

/-- The final local machine with every integer confidence parameter fixed. -/
def confidentMachine (W : ℕ) (delta : ℝ) (hW : 0 < W) : Machine V :=
  let L := confidenceLog (Fintype.card V) W delta
  let Q := canonicalBudget V W L
  canonicalMachine W L (capLog (Fintype.card V) W Q delta) (prefixLog delta)
    hW (confidenceLog_pos _ _ _)

theorem confidentMachine_valid (W : ℕ) (delta : ℝ) (hW : 0 < W) :
    (confidentMachine (V:=V) W delta hW).Valid :=
  canonicalMachine_valid _ _ _ _ _ _

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.actual_confidence_budget
#print axioms RobustMatching.R8StreamingWrapper.confidentMachine_valid
