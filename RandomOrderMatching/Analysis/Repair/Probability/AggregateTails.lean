import RandomOrderMatching.Analysis.Repair.Probability.AggregateMean

/-! The mixed aggregate has one random flag per typed endpoint. Its squared
original-parent range budget is at most four times copy multiplicity times
the number of benchmark pairs, irrespective of unmatched leaf count. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair.Probability
open RandomOrderMatching.Analysis.Repair RandomOrderMatching.Analysis.Repair.Typed

variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]

def originalMultiplicity (p : Parents B G M J R) (b : B) : ℝ :=
  (∑ g, if p.gate g = b then (1 : ℝ) else 0) +
  (∑ m, if p.missing m = b then (1 : ℝ) else 0) +
  (∑ j, if p.internalMissing j = b then (1 : ℝ) else 0) +
  (∑ r, if p.root r = b then (1 : ℝ) else 0)

def randomPairCount (G M J R : Type*) [Fintype G] [Fintype M] [Fintype J] [Fintype R] : ℝ :=
  Fintype.card G + Fintype.card M + Fintype.card J + Fintype.card R

lemma originalMultiplicity_sum (p : Parents B G M J R) :
    ∑ b, originalMultiplicity p b = randomPairCount G M J R := by
  simp only [originalMultiplicity, Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun b m => if p.missing m = b then (1:ℝ) else 0),
    Finset.sum_comm (f := fun b j => if p.internalMissing j = b then (1:ℝ) else 0),
    Finset.sum_comm (f := fun b r => if p.root r = b then (1:ℝ) else 0)]
  simp [randomPairCount]

/-- Both endpoints of every random benchmark pair contribute one flag.
Deterministic vertices mapped to the dummy parent contribute zero. -/
lemma mixed_unweighted_blockRange (p : Parents B G M J R) (b0 b : B) :
    blockRange (mixedParent (P := P) (I := I) (U := U) p b0)
      (fun i => signalRange (mixedSignal i)) b = 2 * originalMultiplicity p b := by
  simp only [blockRange, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, mixedParent, mixedSignal, receiverSignal, senderSignal,
    outsideParent, centerParent, signalRange, Bool.false_eq_true, if_false, if_true,
    ite_self, add_zero, zero_add, Finset.sum_const_zero]
  unfold originalMultiplicity
  simp only [Finset.sum_add_distrib]
  by_cases hb : b0 = b <;> simp only [hb, if_true, if_false, Finset.sum_const_zero,
    add_zero, zero_add]
  all_goals ring

lemma mixed_range_total (p : Parents B G M J R) (b0 : B) :
    (∑ i : MixedIndex G M P I J R U, signalRange (mixedSignal i)) =
      2 * randomPairCount G M J R := by
  rw [← block_range_sum (mixedParent p b0)]
  simp_rw [mixed_unweighted_blockRange]
  rw [← Finset.mul_sum, originalMultiplicity_sum]

lemma mixed_square_range_budget
    (p : Parents B G M J R) (b0 : B)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (hrow : ∀ c, ∑ x, w c x ≤ 1)
    {κ : ℝ} (hk : 0 ≤ κ) (hblock : ∀ b, originalMultiplicity p b ≤ κ) :
    (∑ b, (blockRange (mixedParent p b0)
      (signalRanges mixedSignal (mixedCoefficient w)) b)^2) ≤
      4 * κ * randomPairCount G M J R := by
  have ha (i : MixedIndex G M P I J R U) : 0 ≤ mixedCoefficient w i :=
    (mixedCoefficient_bounds w hw hrow i).1
  have hr (i : MixedIndex G M P I J R U) :
      signalRanges mixedSignal (mixedCoefficient w) i ≤ signalRange (mixedSignal i) :=
    mul_le_of_le_one_left (signalRange_nonneg _) (mixedCoefficient_bounds w hw hrow i).2
  have hb (b : B) : 0 ≤ blockRange (mixedParent p b0)
      (signalRanges mixedSignal (mixedCoefficient w)) b :=
    Finset.sum_nonneg fun i _ => signalRanges_nonneg _ _ ha i
  have hm (b : B) : blockRange (mixedParent p b0)
      (signalRanges mixedSignal (mixedCoefficient w)) b ≤ 2 * κ := by
    calc
      _ ≤ blockRange (mixedParent p b0) (fun i => signalRange (mixedSignal i)) b :=
        Finset.sum_le_sum fun i _ => hr i
      _ = 2 * originalMultiplicity p b := mixed_unweighted_blockRange p b0 b
      _ ≤ 2 * κ := mul_le_mul_of_nonneg_left (hblock b) (by norm_num)
  have hs : (∑ i : MixedIndex G M P I J R U,
      signalRanges mixedSignal (mixedCoefficient w) i) ≤ 2 * randomPairCount G M J R :=
    (Finset.sum_le_sum fun i _ => hr i).trans_eq (mixed_range_total p b0)
  calc
    _ ≤ ∑ b, (2*κ) * blockRange (mixedParent p b0)
        (signalRanges mixedSignal (mixedCoefficient w)) b :=
      Finset.sum_le_sum fun b _ => by nlinarith [hb b, hm b]
    _ = (2*κ) * ∑ i, signalRanges mixedSignal (mixedCoefficient w) i := by
      rw [← Finset.mul_sum, block_range_sum]
    _ ≤ (2*κ) * (2*randomPairCount G M J R) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num) hk)
    _ = _ := by ring

/-- A lower-tail bound for the actual mixed graph quantity. All copies with
the same original parent share its clock. -/
theorem actual_mixed_lower_tail
    (p : Parents B G M J R) (b0 : B)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (hcross : ∀ c x, H c x → sideC c ≠ sideO x)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hsupport : ∀ c x, ¬H c x → w c x = 0)
    (hw : ∀ c x, 0 ≤ w c x) (hrow : ∀ c, ∑ x, w c x ≤ 1)
    {κ μ t : ℝ} (hk : 0 ≤ κ) (hblock : ∀ b, originalMultiplicity p b ≤ κ)
    (hcount : randomPairCount G M J R ≤ μ) (hbudget : 0 < 4*κ*μ) (ht : 0 < t) :
    (experiment (B := B)).real {z | t ≤ outsideProfile alpha omega w -
      ∑ layer : Bool, ∑ x, mixedValue (states p z) alpha omega H sideC sideO w layer x} ≤
      Real.exp (-2*t^2/(4*κ*μ)) := by
  have hsq := (mixed_square_range_budget p b0 w hw hrow hk hblock).trans
    (mul_le_mul_of_nonneg_left hcount (mul_nonneg (by norm_num) hk))
  have hh := signal_lower_tail_budget (mixedParent p b0) mixedSignal (mixedCoefficient w)
    (fun i => (mixedCoefficient_bounds w hw hrow i).1) ht hbudget hsq
  simpa only [mixedExpectation_eq_outsideProfile w hw,
    ← mixedValue_eq_signalSum p b0 _ H sideC sideO hcross w hsupport] using hh

end RandomOrderMatching.Analysis.Repair.Probability
