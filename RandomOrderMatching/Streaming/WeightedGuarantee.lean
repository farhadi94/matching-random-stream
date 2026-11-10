import RandomOrderMatching.Streaming.BoundedGuarantee
import RandomOrderMatching.Weights.Windows.Reduction
noncomputable section
open Classical
open scoped BigOperators
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph RandomOrderMatching.Weights.Windows RandomOrderMatching.Probability.Restriction
variable {V : Type*} [Fintype V] [LinearOrder V]
set_option maxHeartbeats 1000000

/-- Choose the rational accuracy parameter internally. The proved interval
keeps its reciprocal within a constant factor of the requested accuracy. -/
def accuracyParameter (epsilon : ℝ) (he : 0 < epsilon) : ℚ :=
  Classical.choose (exists_rational_accuracy (lt_min he (by norm_num)) (min_le_right epsilon 1))

theorem accuracyParameter_spec (epsilon : ℝ) (he : 0 < epsilon) :
    0 < accuracyParameter epsilon he ∧ accuracyParameter epsilon he ≤ 1 ∧
    min epsilon 1/2 < (accuracyParameter epsilon he:ℝ) ∧
    (accuracyParameter epsilon he:ℝ) ≤ epsilon := by
  have hh := Classical.choose_spec
    (exists_rational_accuracy (lt_min he (by norm_num)) (min_le_right epsilon 1))
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.trans (min_le_left epsilon 1)⟩

def arbitraryParameters (epsilon : ℝ) (he : 0 < epsilon) : Parameters :=
  planned (accuracyParameter epsilon he) (accuracyParameter_spec epsilon he).1
    (accuracyParameter_spec epsilon he).2.1

theorem integerRange_pos (p : Parameters) : 0 < p.integerRange := by
  unfold Parameters.integerRange
  exact Nat.ceil_pos.mpr (div_pos (pow_pos (lt_trans (by norm_num : (0:ℚ)<1) p.base_gt_one) _)
    p.eta_pos)

def localWindowFailure (p : Parameters) (n : ℕ) (delta : ℝ) : ℝ :=
  delta/(max 1 (p.k*n^2):ℕ)

theorem localWindowFailure_range (p : Parameters) (n : ℕ) {delta : ℝ}
    (hd : 0 < delta) (hd1 : delta < 1) :
    0 < localWindowFailure p n delta ∧ localWindowFailure p n delta < 1 := by
  have hc : (1:ℝ) ≤ (max 1 (p.k*n^2):ℕ) := by exact_mod_cast (le_max_left 1 (p.k*n^2))
  have hcp : (0:ℝ) < (max 1 (p.k*n^2):ℕ) := by linarith
  constructor
  · exact div_pos hd hcp
  · apply (div_lt_iff₀ hcp).mpr
    linarith

def arbitraryLocalMachine (epsilon delta : ℝ) (he : 0 < epsilon) : Machine V :=
  let p := arbitraryParameters epsilon he
  confidentMachine p.integerRange (localWindowFailure p (Fintype.card V) delta) (integerRange_pos p)

/-- Total EOF answer, including vertex universes of size zero or one. The
nontrivial branch is exactly the proved live-window retirement decoder. -/
def arbitraryOutput (epsilon delta : ℝ) (he : 0 < epsilon)
    (w : Edge V → ℚ) (l : List (Edge V)) : Graph V :=
  if Fintype.card V ≤ 1 then ∅ else
    (arbitraryParameters epsilon he).answer (arbitraryLocalMachine epsilon delta he) w
      (Fintype.card V) l

def arbitraryStreamOutput (epsilon delta : ℝ) (he : 0 < epsilon)
    (w : Edge V → ℚ) (stream : ℕ → Edge V) (t : ℕ) : Graph V :=
  if Fintype.card V ≤ 1 then ∅ else
    (arbitraryParameters epsilon he).actualAnswer (arbitraryLocalMachine epsilon delta he) w
      (Fintype.card V) stream t

theorem arbitraryStreamOutput_eq (epsilon delta : ℝ) (he : 0 < epsilon)
    (w : Edge V → ℚ) (stream : ℕ → Edge V) (t : ℕ) :
    arbitraryStreamOutput epsilon delta he w stream t=
      arbitraryOutput epsilon delta he w (streamList stream t) := by
  unfold arbitraryStreamOutput arbitraryOutput
  split_ifs
  · rfl
  · exact Parameters.actualAnswer_eq _ _ _ _ _ _

theorem arbitraryOutput_valid (epsilon delta : ℝ) (he : 0 < epsilon)
    (w : Edge V → ℚ) (l : List (Edge V)) :
    Matching (arbitraryOutput epsilon delta he w l) ∧
      arbitraryOutput epsilon delta he w l ⊆ l.toFinset := by
  unfold arbitraryOutput
  split_ifs
  · simp [Matching]
  · apply Parameters.answer_valid
    exact confidentMachine_valid _ _ _

theorem no_edge_on_small_universe (hn : Fintype.card V ≤ 1) (e : Edge V) : False := by
  have hh := Finset.card_le_univ e.val
  rw [e.property] at hh
  omega

/-- Unconditional arbitrary positive rational-weight random-order guarantee.
Accuracy, local failure allocation, and the local bounded machine are all fixed
inside the algorithm; no range or local-success premise is supplied. -/
theorem arbitrary_weight_random_order (epsilon delta : ℝ)
    (he : 0 < epsilon) (hd : 0 < delta) (hd1 : delta < 1)
    (w : Edge V → ℚ) (hw : ∀ e,0 < w e)
    (l : List (Edge V)) (hnd : l.Nodup) (M : Graph V) (hM : IsOptimum w l M) :
    permMean l (fun u => if (finalRatio-epsilon)*(∑ e ∈ M,(w e:ℝ)) ≤
      ∑ e ∈ arbitraryOutput epsilon delta he w u,(w e:ℝ) then 0 else 1) ≤ delta := by
  by_cases hn : Fintype.card V ≤ 1
  · have hl : l=[] := by
      cases l with
      | nil => rfl
      | cons e es => exact (no_edge_on_small_universe hn e).elim
    have hm : M=∅ := by
      apply Finset.Subset.antisymm _ (Finset.empty_subset _)
      intro e he'
      exact (no_edge_on_small_universe hn e).elim
    simp only [hl,hm,arbitraryOutput,if_pos hn,Finset.sum_empty,mul_zero,le_refl,if_true]
    simpa [permMean,List.permutations'] using hd.le
  have hn0 : 0 < Fintype.card V := by omega
  let theta := accuracyParameter epsilon he
  let p := arbitraryParameters epsilon he
  let a := arbitraryLocalMachine (V:=V) epsilon delta he
  have ht := accuracyParameter_spec epsilon he
  have hcount : 0 < p.k*(Fintype.card V)^2 := Nat.mul_pos p.width_pos (pow_pos hn0 2)
  have hlocal := localWindowFailure_range p (Fintype.card V) hd hd1
  have hc : a.Contract p.integerRange finalRatio
      (delta/(p.k*(Fintype.card V)^2:ℕ)) := by
    have hh := confidentMachine_contract (V:=V) p.integerRange (integerRange_pos p)
      (localWindowFailure p (Fintype.card V) delta) hlocal.1 hlocal.2
    change (confidentMachine (V:=V) p.integerRange (localWindowFailure p (Fintype.card V) delta)
      (integerRange_pos p)).Contract p.integerRange finalRatio (delta/(p.k*(Fintype.card V)^2:ℕ))
    have hc1 : 1 ≤ p.k*(Fintype.card V)^2 := Nat.succ_le_iff.mpr hcount
    simpa only [localWindowFailure,max_eq_right hc1] using hh
  have hh := planned_arbitrary_weight hn0 a w hw theta ht.1 ht.2.1
    finalRatio_bounds.1 finalRatio_bounds.2 ht.2.2.2 hd.le hc l hnd M hM
  simpa only [arbitraryOutput,if_neg hn,theta,p,a,arbitraryParameters] using hh

end RandomOrderMatching.Streaming
