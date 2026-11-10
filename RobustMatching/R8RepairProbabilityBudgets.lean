import RobustMatching.R8RepairProbabilitySignalTails

noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RobustMatching.R8RepairProbability
variable {B T : Type*} [Fintype B] [Fintype T]

lemma blockRange_le_card (parent : T → B) (a : T → ℝ) (b : B) {D : ℝ}
    (ha : ∀i, a i≤D) :
    blockRange parent a b ≤ ((Finset.univ.filter fun i => parent i=b ∧ a i≠0).card:ℝ)*D := by
  have he : blockRange parent a b =
      ∑ i ∈ Finset.univ.filter (fun i => parent i=b ∧ a i≠0),a i := by
    simp only [blockRange,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : parent i=b <;> by_cases hz : a i=0 <;> simp [hp,hz]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => parent i=b ∧ a i≠0),D :=
      Finset.sum_le_sum fun i _ => ha i
    _ = _ := by simp

/-- Deterministic vertices contribute zero range and are not charged to a
parent's copy budget, even if all are mapped to the same dummy label. -/
theorem batch_support_square_budget (parent : T → B) (a : T → ℝ) (k : ℕ)
    (hcard : ∀ b,(Finset.univ.filter fun i => parent i=b ∧ a i≠0).card≤k)
    {D S : ℝ} (ha : ∀i,0≤a i) (hD : 0≤D) (hmax : ∀i,a i≤D)
    (hsum : ∑i,a i≤S) :
    ∑b,(blockRange parent a b)^2 ≤ (k:ℝ)*D*S := by
  have hb (b) : 0≤blockRange parent a b := Finset.sum_nonneg fun i _ => ha i
  have hm (b) : blockRange parent a b≤(k:ℝ)*D :=
    (blockRange_le_card parent a b hmax).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard b)) hD)
  calc
    _ ≤ ∑b,((k:ℝ)*D)*blockRange parent a b :=
      Finset.sum_le_sum fun b _ => by nlinarith [hb b,hm b]
    _ = ((k:ℝ)*D)*(∑i,a i) := by rw [←Finset.mul_sum,block_range_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg k) hD)

lemma signalSum_eq_mean_of_zero (parent : T → B) (s : T → Signal) (a : T → ℝ)
    (hz : ∀i,signalRanges s a i=0) (z : B → Clock) :
    signalSum parent s a z=signalExpectation s a := by
  apply Finset.sum_congr rfl
  intro i _
  have hi := hz i
  cases hs : s i <;> simp [signalRanges,signalRange,hs] at hi <;>
    simp [hs,signalValue,signalMean,hi]

lemma ranges_zero_of_budget_zero (parent : T → B) (s : T → Signal) (a : T → ℝ)
    (ha : ∀i,0≤a i)
    (hz : ∑b,(blockRange parent (signalRanges s a) b)^2=0) :
    ∀i,signalRanges s a i=0 := by
  have hb (b) : blockRange parent (signalRanges s a) b=0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b (_:b∈Finset.univ) => sq_nonneg (blockRange parent (signalRanges s a) b))).mp hz
    exact sq_eq_zero_iff.mp (h b (Finset.mem_univ b))
  have hs : ∑i,signalRanges s a i=0 := by
    rw [←block_range_sum parent]
    exact Finset.sum_eq_zero fun b _ => hb b
  intro i
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => signalRanges_nonneg s a ha i)).mp hs
    i (Finset.mem_univ i)

lemma negative_div_exp_mono {x A D : ℝ} (hx : 0≤x) (hA : 0<A) (hAD : A≤D) :
    Real.exp (-x/A)≤Real.exp (-x/D) := by
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff₀ hA (lt_of_lt_of_le hA hAD)).mpr
  nlinarith

/-- A zero square-range budget means the actual random variable is constant;
this handles the zero denominator without replacing a useful bound by one. -/
theorem signal_upper_tail_budget (parent : T → B) (s : T → Signal) (a : T → ℝ)
    (ha : ∀i,0≤a i) {t D : ℝ} (ht : 0<t) (hD : 0<D)
    (hbudget : ∑b,(blockRange parent (signalRanges s a) b)^2≤D) :
    (experiment (B:=B)).real {z | t≤signalSum parent s a z-signalExpectation s a} ≤
      Real.exp (-2*t^2/D) := by
  by_cases hz : ∑b,(blockRange parent (signalRanges s a) b)^2=0
  · have he : {z | t≤signalSum parent s a z-signalExpectation s a}= (∅:Set (B→Clock)) := by
      ext z
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false]
      rw [signalSum_eq_mean_of_zero parent s a (ranges_zero_of_budget_zero parent s a ha hz) z]
      simp [not_le_of_gt ht]
    rw [he]
    simp only [measureReal_empty]
    exact le_of_lt (Real.exp_pos _)
  · have hp : 0<∑b,(blockRange parent (signalRanges s a) b)^2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun b _ => sq_nonneg _) (Ne.symm hz)
    exact (signal_upper_tail parent s a ha (le_of_lt ht)).trans
      (by simpa only [neg_mul] using negative_div_exp_mono (by positivity : 0≤2*t^2) hp hbudget)

theorem signal_lower_tail_budget (parent : T → B) (s : T → Signal) (a : T → ℝ)
    (ha : ∀i,0≤a i) {t D : ℝ} (ht : 0<t) (hD : 0<D)
    (hbudget : ∑b,(blockRange parent (signalRanges s a) b)^2≤D) :
    (experiment (B:=B)).real {z | t≤signalExpectation s a-signalSum parent s a z} ≤
      Real.exp (-2*t^2/D) := by
  by_cases hz : ∑b,(blockRange parent (signalRanges s a) b)^2=0
  · have he : {z | t≤signalExpectation s a-signalSum parent s a z}= (∅:Set (B→Clock)) := by
      ext z
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false]
      rw [signalSum_eq_mean_of_zero parent s a (ranges_zero_of_budget_zero parent s a ha hz) z]
      simp [not_le_of_gt ht]
    rw [he]
    simp only [measureReal_empty]
    exact le_of_lt (Real.exp_pos _)
  · have hp : 0<∑b,(blockRange parent (signalRanges s a) b)^2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun b _ => sq_nonneg _) (Ne.symm hz)
    exact (signal_lower_tail parent s a ha (le_of_lt ht)).trans
      (by simpa only [neg_mul] using negative_div_exp_mono (by positivity : 0≤2*t^2) hp hbudget)

end RobustMatching.R8RepairProbability
