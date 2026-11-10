import RandomOrderMatching.Probability.Batches.Concentration
import RandomOrderMatching.Probability.Batches.FailureBudget
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! An optimum-respecting cut: genuine probability for its independent
single-neighbor orientation blocks, plus the deterministic degree interface.
The finite graph decomposition into these blocks is proved in the manuscript;
no full graph-valued random-cut construction is claimed formalized here. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

namespace RandomOrderMatching.Analysis.BalancedCut.DegreeInterface

noncomputable section

def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- After conditioning on a vertex's own side, a matched pair with two
neighbors contributes exactly one. Only single-neighbor blocks fluctuate. -/
noncomputable def orientationDegree {ι : Type*} [Fintype ι]
    (doubleCount mate : ℕ) (ω : ι → I) : ℝ :=
  doubleCount + mate + ∑ i, clockWeight half 1 (ω i)

def originalDegree {ι : Type*} [Fintype ι] (doubleCount mate : ℕ) : ℝ :=
  2 * doubleCount + Fintype.card ι + mate

theorem orientation_center_identity {ι : Type*} [Fintype ι]
    (doubleCount mate : ℕ) (ω : ι → I) :
    orientationDegree doubleCount mate ω -
      (originalDegree (ι := ι) doubleCount mate / 2 + (mate : ℝ) / 2) =
      ∑ i, (clockWeight half 1 (ω i) - 1 / 2) := by
  simp only [orientationDegree, originalDegree, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Actual probability of the upper deviation in the grouped orientation
model, with a denominator equal to the number of fluctuating blocks. -/
theorem orientation_upper_tail {ι : Type*} [Fintype ι]
    (doubleCount mate : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure I))).real
      {ω | t ≤ orientationDegree doubleCount mate ω -
        (originalDegree (ι := ι) doubleCount mate / 2 + (mate : ℝ) / 2)} ≤
      Real.exp (-2 * t ^ 2 / Fintype.card ι) := by
  simp_rw [orientation_center_identity]
  have h := uniform_clock_weighted_upper_tail (ι := ι) half (fun _ ↦ (1 : ℝ))
    (fun _ ↦ by norm_num) ht
  simpa [half] using h

theorem orientation_lower_tail {ι : Type*} [Fintype ι]
    (doubleCount mate : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure I))).real
      {ω | t ≤ (originalDegree (ι := ι) doubleCount mate / 2 + (mate : ℝ) / 2) -
        orientationDegree doubleCount mate ω} ≤
      Real.exp (-2 * t ^ 2 / Fintype.card ι) := by
  have heq (ω : ι → I) :
      originalDegree (ι := ι) doubleCount mate / 2 + (mate : ℝ) / 2 -
        orientationDegree doubleCount mate ω =
        ∑ i, (1 / 2 - clockWeight half 1 (ω i)) := by
    have h := orientation_center_identity doubleCount mate ω
    calc
      _ = -(orientationDegree doubleCount mate ω -
        (originalDegree (ι := ι) doubleCount mate / 2 + (mate : ℝ) / 2)) := by ring
      _ = -(∑ i, (clockWeight half 1 (ω i) - 1 / 2)) := by rw [h]
      _ = _ := by simp only [← Finset.sum_neg_distrib, neg_sub]
  simp_rw [heq]
  have h := uniform_clock_weighted_lower_tail (ι := ι) half (fun _ ↦ (1 : ℝ))
    (fun _ ↦ by norm_num) ht
  simpa [half] using h

theorem fluctuating_blocks_le_degree {ι : Type*} [Fintype ι]
    (doubleCount mate : ℕ) :
    (Fintype.card ι : ℝ) ≤ originalDegree (ι := ι) doubleCount mate := by
  unfold originalDegree
  linarith [Nat.cast_nonneg (α := ℝ) doubleCount, Nat.cast_nonneg (α := ℝ) mate]

/-- The asymmetric half-degree window includes the possible forced mate,
whose mean bias is one half. -/
theorem centered_window_implies_degree_window {ι : Type*} [Fintype ι]
    (doubleCount mate : ℕ) (hm : mate ≤ 1) (ω : ι → I) (t : ℝ)
    (hl : -t ≤ orientationDegree doubleCount mate ω -
      (originalDegree (ι := ι) doubleCount mate / 2 + (mate : ℝ) / 2))
    (hu : orientationDegree doubleCount mate ω -
      (originalDegree (ι := ι) doubleCount mate / 2 + (mate : ℝ) / 2) ≤ t) :
    originalDegree (ι := ι) doubleCount mate / 2 - t ≤
      orientationDegree doubleCount mate ω ∧
    orientationDegree doubleCount mate ω ≤
      originalDegree (ι := ι) doubleCount mate / 2 + t + 1 / 2 := by
  have hm' : (mate : ℝ) ≤ 1 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ mate := Nat.cast_nonneg _
  constructor <;> linarith

def cutGraph {V : Type*} (H : SimpleGraph V) (side : V → Bool) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ side u ≠ side v
  symm := ⟨by intro u v h; exact ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨by intro v h; exact h.2 rfl⟩

instance {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj] (side : V → Bool) :
    DecidableRel (cutGraph H side).Adj := by
  intro u v
  change Decidable (H.Adj u v ∧ side u ≠ side v)
  infer_instance

theorem cutGraph_le {V : Type*} (H : SimpleGraph V) (side : V → Bool) :
    cutGraph H side ≤ H := fun _ _ h ↦ h.1

theorem cutGraph_bipartite {V : Type*} (H : SimpleGraph V) (side : V → Bool) :
    (cutGraph H side).IsBipartiteWith {v | side v = false} {v | side v = true} := by
  constructor
  · rw [Set.disjoint_left]
    intro v hv hf
    simp only [Set.mem_ofPred_eq] at hv hf
    rw [hv] at hf
    contradiction
  · intro u v h
    rcases h with ⟨_, h⟩
    cases hu : side u <;> cases hv : side v <;> simp_all

def betaCut (beta0 : ℝ) : ℝ := beta0 / 2 + 2 * (1 / 10 ^ 10) * beta0 + 1

/-- This interface is on actual graph degrees. It only assumes the vertexwise
balance window and original edge-degree inequalities, then proves both new
reference inequalities. In particular N is restricted by the same cut; it is
not recomputed using a new underfull rule. -/
theorem cut_degree_interface {V : Type*} [Fintype V]
    (H N : SimpleGraph V) [DecidableRel H.Adj] (side : V → Bool)
    {beta0 : ℝ} (hβ : (10 ^ 22 : ℝ) ≤ beta0)
    (hupper : ∀ u v, H.Adj u v → (H.degree u : ℝ) + H.degree v ≤ beta0)
    (hlower : ∀ u v, N.Adj u v →
      (1 - 1 / 10 ^ 9 : ℝ) * beta0 ≤ (H.degree u : ℝ) + H.degree v)
    (hbal : ∀ v,
      (H.degree v : ℝ) / 2 - (1 / 10 ^ 10 : ℝ) * beta0 ≤
        ((cutGraph H side).degree v : ℝ) ∧
      ((cutGraph H side).degree v : ℝ) ≤
        (H.degree v : ℝ) / 2 + (1 / 10 ^ 10 : ℝ) * beta0 + 1 / 2) :
    (∀ u v, (cutGraph H side).Adj u v →
      ((cutGraph H side).degree u : ℝ) + (cutGraph H side).degree v ≤ betaCut beta0) ∧
    (∀ u v, (cutGraph N side).Adj u v →
      (1 - 1 / 10 ^ 8 : ℝ) * betaCut beta0 ≤
        ((cutGraph H side).degree u : ℝ) + (cutGraph H side).degree v) := by
  constructor
  · intro u v h
    have h0 := hupper u v h.1
    have hu := (hbal u).2
    have hv := (hbal v).2
    unfold betaCut
    linarith
  · intro u v h
    have h0 := hlower u v h.1
    have hu := (hbal u).1
    have hv := (hbal v).1
    unfold betaCut
    nlinarith

theorem betaCut_integer_and_large (k L : ℕ) (_hk : 1 ≤ k) (_hL : 1 ≤ L) :
    betaCut ((10 ^ 22 : ℝ) * k * L) =
      (((5000000002000000000000 : ℕ) * k * L + 1 : ℕ) : ℝ) ∧
    (10 ^ 18 : ℝ) * k * L ≤ betaCut ((10 ^ 22 : ℝ) * k * L) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  constructor
  · simp only [betaCut, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  · unfold betaCut
    nlinarith [mul_nonneg hk0 hL0]

/-- The cut has positive existence probability: the union-bound failure is
strictly below one at the chosen logarithmic scale. -/
theorem cut_failure_lt_one {n δ L k : ℝ}
    (hn : 2 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hL : Real.log (100 * n / δ) ≤ L) (hk : 1 ≤ k) :
    2 * n * Real.exp (-2 * (1 / 10 ^ 10 : ℝ) ^ 2 * (10 ^ 22 * k * L)) < 1 := by
  obtain ⟨hL0, hbase⟩ := batch_failure_base hn hδ hδ1 hL
  have hn0 : 0 < n := by linarith
  have he : -2 * (1 / 10 ^ 10 : ℝ) ^ 2 * (10 ^ 22 * k * L) ≤ -L := by
    nlinarith [mul_le_mul_of_nonneg_right hk hL0]
  have he' := Real.exp_le_exp.mpr he
  have hb : 2 * n * Real.exp (-L) ≤ δ / 50 := by
    calc
      _ ≤ 2 * n * (δ / (100 * n)) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by field_simp; norm_num
  have h := mul_le_mul_of_nonneg_left he' (show 0 ≤ 2 * n by positivity)
  linarith

end
end RandomOrderMatching.Analysis.BalancedCut.DegreeInterface

#print axioms RandomOrderMatching.Analysis.BalancedCut.DegreeInterface.orientation_upper_tail
#print axioms RandomOrderMatching.Analysis.BalancedCut.DegreeInterface.orientation_lower_tail
#print axioms RandomOrderMatching.Analysis.BalancedCut.DegreeInterface.cut_degree_interface
#print axioms RandomOrderMatching.Analysis.BalancedCut.DegreeInterface.betaCut_integer_and_large
#print axioms RandomOrderMatching.Analysis.BalancedCut.DegreeInterface.cut_failure_lt_one
