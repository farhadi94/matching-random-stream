import RandomOrderMatching.Analysis.Repair.Probability.RangeBounds

/-! Actual active/late benchmark counts, with copies grouped by original label. -/
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair.Probability
open RandomOrderMatching.Analysis.Repair.Typed
variable {B T : Type*} [Fintype B] [Fintype T]

lemma count_expectation (s : Signal) :
    signalExpectation (fun _ : T => s) (fun _=>1) = signalMean s*(Fintype.card T:ℝ) := by
  simp [signalExpectation,mul_comm]

lemma count_square_budget (parent : T → B) (s : Signal) (k : ℕ)
    (hcard : ∀b,(Finset.univ.filter fun i=>parent i=b).card≤k) :
    ∑b,(blockRange parent (signalRanges (fun _:T=>s) (fun _=>1)) b)^2 ≤
      (k:ℝ)*(Fintype.card T:ℝ) := by
  have hc (b) : (Finset.univ.filter fun i=>parent i=b ∧
      signalRanges (fun _:T=>s) (fun _=>1) i≠0).card≤k := by
    refine (Finset.card_le_card ?_).trans (hcard b)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,(Finset.mem_filter.mp hi).2.1⟩
  have hs : (∑i:T,signalRanges (fun _=>s) (fun _=>1) i)≤(Fintype.card T:ℝ) := by
    calc
      _ ≤ ∑_:T,(1:ℝ) := Finset.sum_le_sum fun i _=>signalRanges_le _ _ (fun _=>by norm_num) i
      _ = _ := by simp
  simpa only [mul_one] using batch_support_square_budget parent
    (signalRanges (fun _:T=>s) (fun _=>1)) k hc
    (fun i=>signalRanges_nonneg _ _ (fun _=>by norm_num) i) (by norm_num : (0:ℝ)≤1)
    (fun i=>signalRanges_le _ _ (fun _=>by norm_num) i) hs

theorem count_lower_tail (parent : T → B) (s : Signal) (k : ℕ)
    (hcard : ∀b,(Finset.univ.filter fun i=>parent i=b).card≤k)
    {μ t : ℝ} (hk : 0<k) (hμ : 0<μ) (hsize : (Fintype.card T:ℝ)≤μ) (ht : 0<t) :
    (experiment (B:=B)).real {z | signalSum parent (fun _:T=>s) (fun _=>1) z <
      signalMean s*(Fintype.card T:ℝ)-t} ≤ Real.exp (-2*t^2/((k:ℝ)*μ)) := by
  have hb := (count_square_budget parent s k hcard).trans
    (mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg k))
  refine (measureReal_mono ?_).trans (signal_lower_tail_budget parent (fun _:T=>s)
    (fun _=>1) (fun _=>by norm_num) ht (mul_pos (Nat.cast_pos.mpr hk) hμ) hb)
  intro z hz
  change signalSum parent (fun _:T=>s) (fun _=>1) z < signalMean s*(Fintype.card T:ℝ)-t at hz
  change t≤signalExpectation _ _-signalSum _ _ _ z
  rw [count_expectation]
  linarith

variable {G M J R : Type*}
variable [Fintype G] [Fintype M] [Fintype J] [Fintype R]

lemma activeCount_eq (p : Parents B G M J R) (z : B→Clock) :
    (∑g,if (states p z).active g=true then (1:ℝ) else 0) =
      signalSum p.gate (fun _=>.active) (fun _=>1) z := by
  apply Finset.sum_congr rfl
  intro g _
  cases h : activeBit (z (p.gate g)) <;> simp [states,signalValue,bitMass,h]

lemma lateRootCount_eq (p : Parents B G M J R) (z : B→Clock) :
    (∑r,if (states p z).earlyR r=false then (1:ℝ) else 0) =
      signalSum p.root (fun _=>.late) (fun _=>1) z := by
  apply Finset.sum_congr rfl
  intro r _
  cases h : earlyBit (z (p.root r)) <;> simp [states,signalValue,bitMass,h]

lemma lateMissingCount_eq (p : Parents B G M J R) (z : B→Clock) :
    (∑m,if (states p z).earlyM m=false then (1:ℝ) else 0) =
      signalSum p.missing (fun _=>.late) (fun _=>1) z := by
  apply Finset.sum_congr rfl
  intro m _
  cases h : earlyBit (z (p.missing m)) <;> simp [states,signalValue,bitMass,h]

lemma lateInternalCount_eq (p : Parents B G M J R) (z : B→Clock) :
    (∑j,if (states p z).earlyJ j=false then (1:ℝ) else 0) =
      signalSum p.internalMissing (fun _=>.late) (fun _=>1) z := by
  apply Finset.sum_congr rfl
  intro j _
  cases h : earlyBit (z (p.internalMissing j)) <;> simp [states,signalValue,bitMass,h]

end RandomOrderMatching.Analysis.Repair.Probability
