import RobustMatching.R8RepairProbabilityAggregateBounds

/-! All local/count fiber hypotheses follow from the one actual
original-parent benchmark-copy multiplicity bound. -/
noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RobustMatching.R8RepairProbability
open R7ClosedRepair.Typed

variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]

lemma signalRange_count {T : Type*} [Fintype T]
    (parent : T → B) (s : T → Signal) (b : B) :
    ((Finset.univ.filter fun i => parent i = b ∧ signalRange (s i) ≠ 0).card : ℝ) =
      blockRange parent (fun i => signalRange (s i)) b := by
  rw [← Finset.sum_boole]
  simp only [blockRange, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : s i <;> by_cases hp : parent i = b <;> simp [hs, hp, signalRange]

lemma mixed_block_card_le (p : Parents B G M J R) (b0 b : B) (κ : ℕ)
    (hblock : originalMultiplicity p b ≤ κ) :
    (Finset.univ.filter fun i : MixedIndex G M P I J R U =>
      mixedParent p b0 i = b ∧ signalRange (mixedSignal i) ≠ 0).card ≤ 2 * κ := by
  apply Nat.cast_le (α := ℝ) |>.mp
  rw [signalRange_count, mixed_unweighted_blockRange]
  exact_mod_cast mul_le_mul_of_nonneg_left hblock (by norm_num : (0:ℝ) ≤ 2)

lemma pair_fibers_le (p : Parents B G M J R) (κ : ℕ)
    (hblock : ∀ b, originalMultiplicity p b ≤ κ) (b : B) :
    (Finset.univ.filter fun g => p.gate g = b).card ≤ κ ∧
    (Finset.univ.filter fun m => p.missing m = b).card ≤ κ ∧
    (Finset.univ.filter fun j => p.internalMissing j = b).card ≤ κ ∧
    (Finset.univ.filter fun r => p.root r = b).card ≤ κ := by
  have hg : (0:ℝ) ≤ ∑ g, if p.gate g = b then (1:ℝ) else 0 := by positivity
  have hm : (0:ℝ) ≤ ∑ m, if p.missing m = b then (1:ℝ) else 0 := by positivity
  have hj : (0:ℝ) ≤ ∑ j, if p.internalMissing j = b then (1:ℝ) else 0 := by positivity
  have hr : (0:ℝ) ≤ ∑ r, if p.root r = b then (1:ℝ) else 0 := by positivity
  have hh := hblock b
  unfold originalMultiplicity at hh
  simp only [Finset.sum_boole] at hg hm hj hr hh
  constructor
  · exact_mod_cast (show ((Finset.univ.filter fun g => p.gate g = b).card : ℝ) ≤ κ by linarith)
  constructor
  · exact_mod_cast (show ((Finset.univ.filter fun m => p.missing m = b).card : ℝ) ≤ κ by linarith)
  constructor
  · exact_mod_cast (show ((Finset.univ.filter fun j => p.internalMissing j = b).card : ℝ) ≤ κ by linarith)
  · exact_mod_cast (show ((Finset.univ.filter fun r => p.root r = b).card : ℝ) ≤ κ by linarith)

lemma local_receiver_fibers_le
    (p : Parents B G M J R) (b0 : B) (κ : ℕ)
    (hblock : ∀ b, originalMultiplicity p b ≤ κ)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideO : Outsides R M G U → Bool) (layer : Bool)
    (c : Centers G M P I J) (b : B) :
    (Finset.univ.filter fun x => H c x ∧ outsideParent p b0 x = b ∧
      signalRange (receiverSignalAt sideO layer x) ≠ 0).card ≤ 2 * κ := by
  let f : Outsides R M G U → MixedIndex G M P I J R U :=
    fun x => .inl (decide (layer = sideO x), x)
  refine (Finset.card_le_card_of_injOn f ?_ ?_).trans (mixed_block_card_le p b0 b κ (hblock b))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.2.1, hx.2.2⟩
  · intro x hx y hy hxy
    exact congrArg Prod.snd (Sum.inl.inj hxy)

lemma local_sender_fibers_le
    (p : Parents B G M J R) (b0 : B) (κ : ℕ)
    (hblock : ∀ b, originalMultiplicity p b ≤ κ)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideO : Outsides R M G U → Bool) (layer : Bool)
    (x : Outsides R M G U) (b : B) :
    (Finset.univ.filter fun c => H c x ∧ centerParent p b0 c = b ∧
      signalRange (senderSignalAt sideO layer x c) ≠ 0).card ≤ 2 * κ := by
  let f : Centers G M P I J → MixedIndex G M P I J R U :=
    fun c => .inr (decide (layer = sideO x), c)
  refine (Finset.card_le_card_of_injOn f ?_ ?_).trans (mixed_block_card_le p b0 b κ (hblock b))
  · intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hc.2.1, hc.2.2⟩
  · intro c hc d hd hcd
    exact congrArg Prod.snd (Sum.inr.inj hcd)

end RobustMatching.R8RepairProbability
