import RandomOrderMatching.Analysis.Repair.Typed.Deletion

/-! The all-outside/internal-pair profile is derived from actual clipped
graph matchings. The remaining probabilistic hypotheses are separated
into local load events, four clock counts, and one availability sum. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RandomOrderMatching.Analysis.Repair.Typed
open RandomOrderMatching.Analysis.Repair

variable {G M P I J R U : Type*}
variable [Fintype G] [Fintype M] [Fintype P] [Fintype I]
  [Fintype J] [Fintype R] [Fintype U]

def primaryRate (α : ℝ) : Centers G M P I J → ℝ
  | .inl _ => 1-α
  | _ => 1

def secondaryRate (ω : ℝ) : Centers G M P I J → ℝ
  | .inl _ => 0
  | .inr (.inl _) => ω
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr (.inl _))) => 0
  | .inr (.inr (.inr (.inr _))) => ω

def primaryCap (ω : ℝ) : Outsides R M G U → ℝ
  | .inl _ => ω
  | .inr (.inl _) => ω
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr _)) => 1

def secondaryCap (α : ℝ) : Outsides R M G U → ℝ
  | .inr (.inr (.inl _)) => 1-α
  | _ => 1

def primaryLoad (α : ℝ)
    (w : Centers G M P I J → Outsides R M G U → ℝ) (x : Outsides R M G U) : ℝ :=
  ∑ c, primaryRate α c * w c x

def secondaryLoad (ω : ℝ)
    (w : Centers G M P I J → Outsides R M G U → ℝ) (x : Outsides R M G U) : ℝ :=
  ∑ c, secondaryRate ω c * w c x

def meanLoad (α ω : ℝ)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U) : ℝ :=
  if layer = sideO x then primaryLoad α w x else secondaryLoad ω w x

def capacity (α ω : ℝ) (sideO : Outsides R M G U → Bool)
    (layer : Bool) (x : Outsides R M G U) : ℝ :=
  if layer = sideO x then primaryCap ω x else secondaryCap α x

def normalizer (α ω : ℝ) (sideO : Outsides R M G U → Bool)
    (layer : Bool) (x : Outsides R M G U) : ℝ :=
  if capacity α ω sideO layer x = 0 then 1 else capacity α ω sideO layer x

def liveReceiver (s : States G M J R) (sideO : Outsides R M G U → Bool)
    (layer : Bool) (x : Outsides R M G U) : Prop :=
  outsideSurvives s sideO layer x ∧ ¬outsideOccupied s x

lemma capacity_nonneg (α ω : ℝ) (ha : α < 1) (hw : 0 < ω)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U) :
    0 ≤ capacity α ω sideO layer x := by
  unfold capacity
  split_ifs <;> rcases x with r | m | g | u <;>
    simp only [primaryCap, secondaryCap] <;> linarith

lemma normalizer_pos (α ω : ℝ) (ha : α < 1) (hw : 0 < ω)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U) :
    0 < normalizer α ω sideO layer x := by
  unfold normalizer
  split_ifs with hh
  · norm_num
  · exact lt_of_le_of_ne (capacity_nonneg α ω ha hw sideO layer x) (Ne.symm hh)

lemma live_capacity_pos (s : States G M J R) (α ω : ℝ)
    (ha : α < 1) (hw : 0 < ω)
    (sideO : Outsides R M G U → Bool) (layer : Bool)
    (x : Outsides R M G U) (hx : liveReceiver s sideO layer x) :
    0 < capacity α ω sideO layer x := by
  rcases x with r | m | g | u
  · unfold capacity
    split_ifs <;> simp only [primaryCap, secondaryCap] <;> linarith
  · unfold capacity
    split_ifs <;> simp only [primaryCap, secondaryCap] <;> linarith
  · have hn : layer ≠ sideO (.inr (.inr (.inl g))) := by
      intro he
      have ha0 : s.active g = false := by
        cases h : s.active g
        · rfl
        · exact False.elim (hx.2 h)
      exact hx.1 ⟨ha0, he.symm⟩
    simp [capacity, hn, secondaryCap, sub_pos.mpr ha]
  · unfold capacity
    split_ifs <;> norm_num [primaryCap, secondaryCap]

def outsideProfile (α ω : ℝ)
    (w : Centers G M P I J → Outsides R M G U → ℝ) : ℝ :=
  ∑ x, (min (primaryLoad α w x) (primaryCap ω x) +
    min (secondaryLoad ω w x) (secondaryCap α x))

def profile (α ω : ℝ)
    (w : Centers G M P I J → Outsides R M G U → ℝ) : ℝ :=
  ((1+α)*(Fintype.card G : ℝ) +
    (1-ω)*((Fintype.card M : ℝ)+(Fintype.card R : ℝ)+(Fintype.card J : ℝ)) +
    (Fintype.card I : ℝ) + outsideProfile α ω w) / 2

def availabilityValue (s : States G M J R) (α ω : ℝ)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (sideO : Outsides R M G U → Bool) (layer : Bool) (x : Outsides R M G U) : ℝ :=
  receiverTarget (liveReceiver s sideO layer) (meanLoad α ω w sideO layer)
    (capacity α ω sideO layer) x

/-- A single actual deletion graph on a simultaneous local-load event. -/
theorem typed_rank_local
    (s : States G M J R) (α ω : ℝ) (ha : α < 1) (hω : 0 < ω)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (layer : Bool)
    (errC : Centers G M P I J → ℝ) (errO : Outsides R M G U → ℝ)
    (heC : ∀ c, 0 ≤ errC c) (heO : ∀ x, 0 ≤ errO x)
    (hlC : ∀ c, rowLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) c ≤
      1 + errC c)
    (hlO : ∀ x, liveReceiver s sideO layer x →
      meanLoad α ω w sideO layer x / capacity α ω sideO layer x - errO x ≤
        colLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) x) :
    (∑ g, if s.active g = true then (1 : ℝ) else 0) +
      (∑ x, availabilityValue s α ω w sideO layer x) -
      (∑ x, errO x) - (∑ c, errC c) ≤
      (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s H sideC sideO layer)) : ℝ) := by
  obtain ⟨T, hT, hm, hv⟩ := actual_typed_matching s H sideC sideO w
    (normalizer α ω sideO) hw (normalizer_pos α ω ha hω sideO) layer
  have hr : (T.card : ℝ) ≤
      (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s H sideC sideO layer)) : ℝ) := by
    exact_mod_cast RandomOrderMatching.Graph.matching_card_le_rank hT hm
  have hf := raw_nonneg s H sideC sideO w (normalizer α ω sideO) hw
    (normalizer_pos α ω ha hω sideO) layer
  have ho := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Outsides R M G U))) =>
    receiver_target_lower _ hf (liveReceiver s sideO layer)
      (meanLoad α ω w sideO layer) (capacity α ω sideO layer) errO heO
      (live_capacity_pos s α ω ha hω sideO layer) hlO x)
  have hc := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Centers G M P I J))) =>
    center_overload_upper _ errC heC hlC c)
  rw [Finset.sum_sub_distrib] at ho
  change (∑ x, availabilityValue s α ω w sideO layer x) - (∑ x, errO x) ≤ _ at ho
  linarith

/-- Low unmatched receivers need no individual concentration event. The
criterion is their actual unscaled support load; the degree criterion
a<=1/2 implies this by the capped-incidence theorem. -/
def lowUnmatched
    (w : Centers G M P I J → Outsides R M G U → ℝ) : Outsides R M G U → Prop
  | .inr (.inr (.inr u)) => (∑ c, w c (.inr (.inr (.inr u)))) ≤ 1
  | _ => False

lemma low_unmatched_raw_upper
    (s : States G M J R) (α ω : ℝ)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (layer : Bool) (x : Outsides R M G U)
    (hx : lowUnmatched w x) :
    colLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) x ≤ 1 := by
  rcases x with r | m | g | u
  · exact False.elim hx
  · exact False.elim hx
  · exact False.elim hx
  · have hn : normalizer α ω sideO layer (.inr (.inr (.inr u))) = 1 := by
      unfold normalizer capacity
      split_ifs <;> norm_num [primaryCap, secondaryCap] at *
    have hterm : ∀ c, rawSupport s H sideC sideO w (normalizer α ω sideO)
        layer c (.inr (.inr (.inr u))) ≤ w c (.inr (.inr (.inr u))) := by
      intro c
      unfold rawSupport
      split_ifs
      · rw [hn, div_one]
      · exact hw c _
    exact (Finset.sum_le_sum fun c _ => hterm c).trans hx

def mixedValue
    (s : States G M J R) (α ω : ℝ)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (layer : Bool) (x : Outsides R M G U) : ℝ :=
  if lowUnmatched w x then
    colLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) x
  else availabilityValue s α ω w sideO layer x

lemma mixed_receiver_lower
    (s : States G M J R) (α ω : ℝ) (ha : α < 1) (hω : 0 < ω)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (layer : Bool)
    (errO : Outsides R M G U → ℝ) (heO : ∀ x, 0 ≤ errO x)
    (hlO : ∀ x, ¬lowUnmatched w x → liveReceiver s sideO layer x →
      meanLoad α ω w sideO layer x / capacity α ω sideO layer x - errO x ≤
        colLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) x)
    (x : Outsides R M G U) :
    mixedValue s α ω H sideC sideO w layer x - errO x ≤
      min (colLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) x) 1 := by
  unfold mixedValue
  split_ifs with hx
  · rw [min_eq_left (low_unmatched_raw_upper s α ω H sideC sideO w hw layer x hx)]
    linarith [heO x]
  · unfold availabilityValue receiverTarget
    split_ifs with hlive
    · exact scaled_receiver_lower (live_capacity_pos s α ω ha hω sideO layer x hlive)
        (heO x) (hlO x hx hlive)
    · have hn : 0 ≤ colLoad
          (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) x := by
        exact Finset.sum_nonneg fun c _ => raw_nonneg s H sideC sideO w
          (normalizer α ω sideO) hw (normalizer_pos α ω ha hω sideO) layer c x
      have hm := le_min hn (by norm_num : (0:ℝ) ≤ 1)
      linarith [heO x]

theorem typed_rank_mixed
    (s : States G M J R) (α ω : ℝ) (ha : α < 1) (hω : 0 < ω)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (layer : Bool)
    (errC : Centers G M P I J → ℝ) (errO : Outsides R M G U → ℝ)
    (heC : ∀ c, 0 ≤ errC c) (heO : ∀ x, 0 ≤ errO x)
    (hlC : ∀ c, rowLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) c ≤
      1 + errC c)
    (hlO : ∀ x, ¬lowUnmatched w x → liveReceiver s sideO layer x →
      meanLoad α ω w sideO layer x / capacity α ω sideO layer x - errO x ≤
        colLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) x) :
    (∑ g, if s.active g = true then (1 : ℝ) else 0) +
      (∑ x, mixedValue s α ω H sideC sideO w layer x) -
      (∑ x, errO x) - (∑ c, errC c) ≤
      (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s H sideC sideO layer)) : ℝ) := by
  obtain ⟨T, hT, hm, hv⟩ := actual_typed_matching s H sideC sideO w
    (normalizer α ω sideO) hw (normalizer_pos α ω ha hω sideO) layer
  have hr : (T.card : ℝ) ≤
      (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s H sideC sideO layer)) : ℝ) := by
    exact_mod_cast RandomOrderMatching.Graph.matching_card_le_rank hT hm
  have ho := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Outsides R M G U))) =>
    mixed_receiver_lower s α ω ha hω H sideC sideO w hw layer errO heO hlO x)
  have hc := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Centers G M P I J))) =>
    center_overload_upper _ errC heC hlC c)
  rw [Finset.sum_sub_distrib] at ho
  linarith

def totalError
    (errC : Bool → Centers G M P I J → ℝ)
    (errO : Bool → Outsides R M G U → ℝ)
    (noiseG noiseR noiseM noiseJ noiseAvailability : ℝ) : ℝ :=
  noiseG + noiseR + noiseM + noiseJ + noiseAvailability +
    (∑ layer : Bool, ∑ c, errC layer c) + (∑ layer : Bool, ∑ x, errO layer x)

/-- The actual support-to-profile theorem. The hypothesis `htransfer`
is precisely the independently proved cut/historical structural bound.
The other non-graph hypotheses are named local/aggregate random events;
none assumes the desired whole profile inequality. -/
theorem actual_profile_bound
    (s : States G M J R) (α ω : ℝ) (ha : α < 1) (hω : 0 < ω)
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x)
    (errC : Bool → Centers G M P I J → ℝ)
    (errO : Bool → Outsides R M G U → ℝ)
    (heC : ∀ layer c, 0 ≤ errC layer c) (heO : ∀ layer x, 0 ≤ errO layer x)
    (hlC : ∀ layer c,
      rowLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) c ≤
        1 + errC layer c)
    (hlO : ∀ layer x, ¬lowUnmatched w x → liveReceiver s sideO layer x →
      meanLoad α ω w sideO layer x / capacity α ω sideO layer x - errO layer x ≤
        colLoad (rawSupport s H sideC sideO w (normalizer α ω sideO) layer) x)
    (noiseG noiseR noiseM noiseJ noiseAvailability V : ℝ)
    (hG : α * (Fintype.card G : ℝ) - noiseG ≤
      ∑ g, if s.active g = true then (1 : ℝ) else 0)
    (hR : (1-ω) * (Fintype.card R : ℝ) - noiseR ≤
      ∑ r, if s.earlyR r = false then (1 : ℝ) else 0)
    (hM : (1-ω) * (Fintype.card M : ℝ) - noiseM ≤
      ∑ m, if s.earlyM m = false then (1 : ℝ) else 0)
    (hJ : (1-ω) * (Fintype.card J : ℝ) - noiseJ ≤
      ∑ j, if s.earlyJ j = false then (1 : ℝ) else 0)
    (hAvailability : outsideProfile α ω w - noiseAvailability ≤
      ∑ layer : Bool, ∑ x, mixedValue s α ω H sideC sideO w layer x)
    (htransfer :
      (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s H sideC sideO false)) : ℝ) +
      (RandomOrderMatching.Graph.rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s H sideC sideO true)) : ℝ) +
      ((selectedEdges (P := P) (I := I) (U := U) s).card : ℝ) ≤ 2*V)
    (hbase : (Fintype.card (Centers G M P I J) : ℝ) ≤ V) :
    max (Fintype.card (Centers G M P I J) : ℝ)
      (profile α ω w -
        totalError errC errO noiseG noiseR noiseM noiseJ noiseAvailability / 2) ≤ V := by
  have h0 := typed_rank_mixed s α ω ha hω H sideC sideO w hw false
    (errC false) (errO false) (heC false) (heO false) (hlC false) (hlO false)
  have h1 := typed_rank_mixed s α ω ha hω H sideC sideO w hw true
    (errC true) (errO true) (heC true) (heO true) (hlC true) (hlO true)
  have hb := exact_bare_credit (P := P) (I := I) (U := U) s
  apply max_le hbase
  simp only [Fintype.sum_bool] at hAvailability
  unfold profile totalError
  simp only [Fintype.sum_bool]
  nlinarith

/-- The directly derived profile is exactly the loss/refund expression
used by the finite typed incidence LP, including the two internal types. -/
theorem profile_loss_form (α ω : ℝ)
    (w : Centers G M P I J → Outsides R M G U → ℝ) :
    profile α ω w = (Fintype.card (Centers G M P I J) : ℝ) -
      ((1-α)*(Fintype.card G : ℝ) + (1+ω)*(Fintype.card M : ℝ) +
        2*(Fintype.card P : ℝ) + 4*(Fintype.card I : ℝ) + 4*(Fintype.card J : ℝ))/2 +
      (outsideProfile α ω w + (1-ω)*(Fintype.card R : ℝ) +
        (Fintype.card I : ℝ) + (1-ω)*(Fintype.card J : ℝ))/2 := by
  rw [center_count]
  push_cast
  unfold profile
  ring

end RandomOrderMatching.Analysis.Repair.Typed
