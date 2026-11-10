import RandomOrderMatching.Probability.ClockCoupling.Construction
import RandomOrderMatching.Analysis.Repair.Probability.RangeBounds

/-! Finite categorical cutoff brackets, counted on original labels.
The cutoff can be selected by any deterministic grid arithmetic. -/
noncomputable section
set_option maxHeartbeats 800000
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Probability.ClockCoupling
open RandomOrderMatching.Analysis.Repair.Probability RandomOrderMatching.Analysis.Repair.Typed

def activeCount {B : Type*} [Fintype B] (z : B → Clock) : ℕ :=
  (Finset.univ.filter fun b => z b = 0).card

def earlyCount {B : Type*} [Fintype B] (z : B → Clock) : ℕ :=
  (Finset.univ.filter fun b => z b ≠ 2).card

def cutoffBracket {B : Type*} [Fintype B] (c : ℕ) (z : B → Clock) : Prop :=
  activeCount z ≤ c ∧ c ≤ earlyCount z

lemma activeCount_signal {B : Type*} [Fintype B] (z : B → Clock) :
    (activeCount z : ℝ) = signalSum id (fun _ : B => Signal.active) (fun _ => 1) z := by
  unfold activeCount signalSum
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro b _
  simp [signalValue, activeBit, bitMass]

lemma earlyCount_signal {B : Type*} [Fintype B] (z : B → Clock) :
    (earlyCount z : ℝ) = signalSum id (fun _ : B => Signal.early) (fun _ => 1) z := by
  unfold earlyCount signalSum
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro b _
  simp [signalValue, earlyBit, bitMass]

lemma activeCount_upper_tail {B : Type*} [Fintype B]
    (hn : 0 < Fintype.card B) {t : ℝ} (ht : 0 < t) :
    (experiment (B := B)).real {z | t ≤ (activeCount z : ℝ) - alpha * Fintype.card B} ≤
      Real.exp (-2*t^2/Fintype.card B) := by
  have hs : (∑ b : B, (blockRange id
      (signalRanges (fun _ : B => Signal.active) (fun _ => 1)) b)^2) = Fintype.card B := by
    have hf (b : B) : Finset.univ.filter (fun i : B => i = b) = {b} := by ext i; simp
    simp [signalRanges, signalRange, blockRange, hf]
  have h := signal_upper_tail_budget id (fun _ : B => Signal.active) (fun _ => 1)
    (fun _ => by norm_num) ht (Nat.cast_pos.mpr hn) (le_of_eq hs)
  simpa only [← activeCount_signal, signalExpectation, signalMean, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_comm] using h

lemma earlyCount_lower_tail {B : Type*} [Fintype B]
    (hn : 0 < Fintype.card B) {t : ℝ} (ht : 0 < t) :
    (experiment (B := B)).real {z | t ≤ omega * Fintype.card B - (earlyCount z : ℝ)} ≤
      Real.exp (-2*t^2/Fintype.card B) := by
  have hs : (∑ b : B, (blockRange id
      (signalRanges (fun _ : B => Signal.early) (fun _ => 1)) b)^2) = Fintype.card B := by
    have hf (b : B) : Finset.univ.filter (fun i : B => i = b) = {b} := by ext i; simp
    simp [signalRanges, signalRange, blockRange, hf]
  have h := signal_lower_tail_budget id (fun _ : B => Signal.early) (fun _ => 1)
    (fun _ => by norm_num) ht (Nat.cast_pos.mpr hn) (le_of_eq hs)
  simpa only [← earlyCount_signal, signalExpectation, signalMean, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_comm] using h

/-- With a deterministic additive margin on each side, the actual count
bracket fails with at most the sum of two original-label Hoeffding tails. -/
theorem cutoffBracket_failure {B : Type*} [Fintype B]
    (hn : 0 < Fintype.card B) (c : ℕ) {t : ℝ} (ht : 0 < t)
    (hleft : alpha * Fintype.card B + t ≤ c)
    (hright : (c : ℝ) ≤ omega * Fintype.card B - t) :
    (experiment (B := B)).real {z | ¬cutoffBracket c z} ≤
      2 * Real.exp (-2*t^2/Fintype.card B) := by
  have hin : {z : B → Clock | ¬cutoffBracket c z} ⊆
      {z | t ≤ (activeCount z : ℝ) - alpha * Fintype.card B} ∪
      {z | t ≤ omega * Fintype.card B - (earlyCount z : ℝ)} := by
    intro z hz
    change ¬(activeCount z ≤ c ∧ c ≤ earlyCount z) at hz
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_cases hl : activeCount z ≤ c
    · right
      have he : earlyCount z < c := by omega
      have hc : (earlyCount z : ℝ) < c := Nat.cast_lt.mpr he
      linarith
    · left
      have he : c < activeCount z := by omega
      have hc : (c : ℝ) < activeCount z := Nat.cast_lt.mpr he
      linarith
  refine (measureReal_mono hin).trans ((measureReal_union_le _ _).trans ?_)
  have ha := activeCount_upper_tail (B := B) hn ht
  have he := earlyCount_lower_tail (B := B) hn ht
  linarith

theorem coupled_cutoffBracket_failure {n : ℕ} (hn : 0 < n) (c : ℕ)
    {t : ℝ} (ht : 0 < t) (hleft : alpha*n+t ≤ c) (hright : (c:ℝ) ≤ omega*n-t) :
    (coupling n).real {s | ¬cutoffBracket c (coupledClocks s)} ≤
      2 * Real.exp (-2*t^2/n) := by
  have hm := (coupledClocks_preserving n).measure_preimage
    (Set.toFinite {z | ¬cutoffBracket c z}).measurableSet.nullMeasurableSet
  have hreal := congrArg ENNReal.toReal hm
  change (coupling n).real {s | ¬cutoffBracket c (coupledClocks s)} =
    (experiment (B := Fin n)).real {z | ¬cutoffBracket c z} at hreal
  rw [hreal]
  simpa only [Fintype.card_fin] using cutoffBracket_failure
    (B := Fin n) (by simpa using hn) c ht (by simpa using hleft) (by simpa using hright)

end RandomOrderMatching.Probability.ClockCoupling
