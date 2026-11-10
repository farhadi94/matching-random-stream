import RobustMatching.R4WeightMembership
import RobustMatching.R6FableImportancePhase

/-! Whole-window retirement on concrete finite stream prefixes.
The local transition is arbitrary: correctness is pointwise in all seeds.
No random-order or approximation conclusion is assumed by these lemmas. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7ReductionRetirement

variable {E I S : Type*}

def fullState (initial : I → S) (step : I → S → E → S)
    (belongs : I → E → Bool) (stream : ℕ → E) : ℕ → I → S :=
  Nat.rec initial (fun n prev i =>
    if belongs i (stream n) then step i (prev i) (stream n) else prev i)

def retiredState (initial : I → S) (step : I → S → E → S)
    (belongs : I → E → Bool) (stream : ℕ → E)
    (threshold : ℕ → ℝ) (upper : I → ℝ) : ℕ → I → S := by
  classical
  exact Nat.rec initial (fun n prev i =>
    if threshold (n+1) < upper i then
      if belongs i (stream n) then step i (prev i) (stream n) else prev i
    else initial i)

/-- Every surviving window is exactly its full, unretired execution. -/
theorem surviving_state_eq_full (initial : I → S) (step : I → S → E → S)
    (belongs : I → E → Bool) (stream : ℕ → E)
    (threshold : ℕ → ℝ) (upper : I → ℝ) (hmono : Monotone threshold)
    (n : ℕ) (i : I) (hlive : threshold n < upper i) :
    retiredState initial step belongs stream threshold upper n i =
      fullState initial step belongs stream n i := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : threshold n < upper i :=
      (hmono (Nat.le_succ n)).trans_lt hlive
    have heq := ih hprev
    simp only [retiredState, fullState]
    simp only [show threshold (n+1) < upper i from hlive, if_true]
    change (if belongs i (stream n) then
        step i (retiredState initial step belongs stream threshold upper n i) (stream n)
      else retiredState initial step belongs stream threshold upper n i) = _
    rw [heq]
    rfl

def prefixMax (weight : E → ℝ) (stream : ℕ → E) : ℕ → ℝ :=
  Nat.rec 0 (fun n previous => max previous (weight (stream n)))

theorem prefixMax_step (weight : E → ℝ) (stream : ℕ → E) (n : ℕ) :
    prefixMax weight stream n ≤ prefixMax weight stream (n+1) :=
  le_max_left _ _

theorem prefixMax_mono (weight : E → ℝ) (stream : ℕ → E) :
    Monotone (prefixMax weight stream) := monotone_nat_of_le_succ (prefixMax_step weight stream)

theorem prefixMax_nonneg (weight : E → ℝ) (stream : ℕ → E) (n : ℕ) :
    0 ≤ prefixMax weight stream n := (prefixMax_mono weight stream) (Nat.zero_le n)

theorem weight_le_prefixMax (weight : E → ℝ) (stream : ℕ → E) {j n : ℕ}
    (hjn : j < n) : weight (stream j) ≤ prefixMax weight stream n := by
  exact (le_max_right (prefixMax weight stream j) (weight (stream j))).trans
    (prefixMax_mono weight stream (Nat.succ_le_iff.mpr hjn))

theorem threshold_mono (weight : E → ℝ) (stream : ℕ → E) {c : ℝ} (hc : 0 ≤ c) :
    Monotone (fun n => c * prefixMax weight stream n) := by
  intro m n hmn
  exact mul_le_mul_of_nonneg_left (prefixMax_mono weight stream hmn) hc

/-- Instantiation by the implemented running maximum; no survival conditioning. -/
theorem running_max_survivor (initial : I → S) (step : I → S → E → S)
    (belongs : I → E → Bool) (stream : ℕ → E) (weight : E → ℝ)
    (upper : I → ℝ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (i : I)
    (hlive : c * prefixMax weight stream n < upper i) :
    retiredState initial step belongs stream
        (fun n => c * prefixMax weight stream n) upper n i =
      fullState initial step belongs stream n i :=
  surviving_state_eq_full initial step belongs stream _ upper
    (threshold_mono weight stream hc) n i hlive

theorem no_revival (threshold : ℕ → ℝ) (hmono : Monotone threshold)
    {u : ℝ} {m n : ℕ} (hmn : m ≤ n) (hdead : u ≤ threshold m) :
    u ≤ threshold n := hdead.trans (hmono hmn)

/-- A heavy original belongs only to surviving half-open windows. -/
theorem heavy_window_survives {w lower upper threshold : ℝ}
    (hwindow : lower ≤ w ∧ w < upper) (hheavy : threshold ≤ w) :
    threshold < upper := hheavy.trans_lt hwindow.2

/-- Alice's smaller threshold retains every window required globally. -/
theorem local_max_contains_global_heavy {w u maxLocal maxGlobal c : ℝ}
    (hc : 0 ≤ c) (hmax : maxLocal ≤ maxGlobal)
    (hheavy : c * maxGlobal ≤ w) (hupper : w < u) : c * maxLocal < u :=
  (mul_le_mul_of_nonneg_left hmax hc).trans_lt (hheavy.trans_lt hupper)

open RobustMatching.R4WeightDyadic RobustMatching.R4WeightTruncation

/-- A finite set of live dyadic windows has a hard range-free count.
`s` is any integer with `2^(-s) ≤ c`; one may choose ceil(log₂(1/c)). -/
theorem live_window_count (T : Finset ℤ) {k s : ℕ} {c m : ℝ}
    (hm : 0 < m) (hc : (2:ℝ)^(-(s:ℤ)) ≤ c)
    (hT : ∀ t ∈ T, lo t ≤ m ∧ c*m < up k t) :
    T.card ≤ k+s+1 := by
  apply integer_diameter_card T (k+s)
  intro i hi j hj
  have hi' := hT i hi
  have hj' := hT j hj
  by_contra hn
  have hexp : i+(k:ℤ) ≤ j-(s:ℤ) := by omega
  have hpow : up k i ≤ lo (j-(s:ℤ)) := lo_mono hexp
  have hfactor : lo (j-(s:ℤ)) = (2:ℝ)^(-(s:ℤ)) * lo j := by
    simp [lo, sub_eq_add_neg, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), mul_comm]
  rw [hfactor] at hpow
  have hpos : 0 ≤ (2:ℝ)^(-(s:ℤ)) := (zpow_pos (by norm_num) _).le
  have hm1 := mul_le_mul_of_nonneg_left hj'.1 hpos
  have hm2 := mul_le_mul_of_nonneg_right hc hm.le
  exact (not_lt_of_ge (hpow.trans (hm1.trans hm2))) hi'.2

/-- The same hard count for arbitrary geometric base. -/
theorem live_window_count_base (T : Finset ℤ) {k s : ℕ} {B c m : ℝ}
    (hB : 1 < B) (hm : 0 < m) (hc : B^(-(s:ℤ)) ≤ c)
    (hT : ∀ t ∈ T, B^t ≤ m ∧ c*m < B^(t+(k:ℤ))) :
    T.card ≤ k+s+1 := by
  apply integer_diameter_card T (k+s)
  intro i hi j hj
  have hi' := hT i hi
  have hj' := hT j hj
  by_contra hn
  have hexp : i+(k:ℤ) ≤ j-(s:ℤ) := by omega
  have hpow : B^(i+(k:ℤ)) ≤ B^(j-(s:ℤ)) := zpow_le_zpow_right₀ hB.le hexp
  have hB0 : 0 < B := by linarith
  have hfactor : B^(j-(s:ℤ)) = B^(-(s:ℤ)) * B^j := by
    rw [sub_eq_add_neg,zpow_add₀ hB0.ne']
    ring
  rw [hfactor] at hpow
  have hm1 := mul_le_mul_of_nonneg_left hj'.1 (zpow_pos hB0 (-(s:ℤ))).le
  have hm2 := mul_le_mul_of_nonneg_right hc hm.le
  exact (not_lt_of_ge (hpow.trans (hm1.trans hm2))) hi'.2

open RobustMatching.R2Cut

theorem matching_card_bound {V : Type*} [Fintype V] [DecidableEq V]
    (M : Graph V) (hM : Matching M) : 2*M.card ≤ Fintype.card V := by
  rw [← covered_card hM]
  exact Finset.card_le_univ _

/-- Discarding edges lighter than a threshold loses at most n*threshold/2. -/
theorem heavy_matching_loss {V : Type*} [Fintype V] [DecidableEq V]
    (M : Graph V) (hM : Matching M) (w : Edge V → ℝ)
    {tau : ℝ} (htau : 0 ≤ tau) :
    (∑ e ∈ M, w e) - (Fintype.card V : ℝ)*tau/2 ≤
      ∑ e ∈ M.filter (fun e => tau ≤ w e), w e := by
  classical
  let L := M.filter (fun e => ¬ tau ≤ w e)
  have hsplit : (∑ e ∈ M, w e) =
      (∑ e ∈ M.filter (fun e => tau ≤ w e), w e) + ∑ e ∈ L, w e := by
    exact (Finset.sum_filter_add_sum_filter_not M (fun e => tau ≤ w e) w).symm
  have hl : (∑ e ∈ L, w e) ≤ (L.card:ℝ)*tau := by
    calc
      _ ≤ ∑ _e ∈ L, tau := Finset.sum_le_sum (fun e he =>
        (lt_of_not_ge (Finset.mem_filter.mp he).2).le)
      _ = _ := by simp
  have hc : 2*L.card ≤ Fintype.card V :=
    matching_card_bound L (matching_mono hM (Finset.filter_subset _ _))
  have hcr : 2*(L.card:ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast hc
  nlinarith

end RobustMatching.R7ReductionRetirement

#print axioms RobustMatching.R7ReductionRetirement.running_max_survivor
#print axioms RobustMatching.R7ReductionRetirement.live_window_count
#print axioms RobustMatching.R7ReductionRetirement.heavy_matching_loss
