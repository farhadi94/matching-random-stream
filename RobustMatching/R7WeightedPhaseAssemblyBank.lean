import RobustMatching.R7WeightedPhaseAssemblyState

/-! The actual retained union, maximum-weight output matching, and record
accounting of a concrete finite bank of original-label phases. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7WeightedPhaseAssembly
open RobustMatching.R2Cut RobustMatching.R7WeightedPhase RobustMatching.R6FableImportance
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]

def activeCuts (cuts : Finset ℕ) (stream : List (Edge V)) : Finset ℕ :=
  cuts.filter (fun c => c ≤ stream.length)

def bankSupport (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) : Graph V :=
  sharedBase H eligible stream ∪
    (activeCuts cuts stream).biUnion (phaseFinal w H eligible stream)

/-- Shared parent records plus each phase's newly retained originals.
An initial phase support is a view of shared records, not a duplicated graph. -/
def bankRecordCount (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) : ℕ :=
  (sharedBase H eligible stream).card +
    ∑ c ∈ activeCuts cuts stream,
      (phaseFinal w H eligible stream c \ initial H eligible stream c).card

def decode (w : Edge V → ℕ) (G : Graph V) : Graph V :=
  Classical.choose (natOpt_attained w G)

def outputMatching (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) : Graph V :=
  decode w (bankSupport w H eligible stream cuts)

theorem decode_subset (w : Edge V → ℕ) (G : Graph V) : decode w G ⊆ G :=
  (Classical.choose_spec (natOpt_attained w G)).1

theorem decode_matching (w : Edge V → ℕ) (G : Graph V) : Matching (decode w G) :=
  (Classical.choose_spec (natOpt_attained w G)).2.1

theorem decode_weight (w : Edge V → ℕ) (G : Graph V) :
    (∑ e ∈ decode w G, w e) = natOpt w G :=
  (Classical.choose_spec (natOpt_attained w G)).2.2

theorem decode_real_weight (w : Edge V → ℕ) (G : Graph V) :
    (∑ e ∈ decode w G, (w e : ℝ)) = opt (fun e => (w e : ℝ)) G := by
  rw [opt_eq_natOpt]
  exact_mod_cast decode_weight w G

theorem shared_subset_bank (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) :
    sharedBase H eligible stream ⊆ bankSupport w H eligible stream cuts :=
  Finset.subset_union_left

theorem phase_subset_bank (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (c : ℕ) (hc : c ∈ activeCuts cuts stream) :
    phaseFinal w H eligible stream c ⊆ bankSupport w H eligible stream cuts := by
  intro e he
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c,hc,he⟩)

theorem shared_subset_input (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) : sharedBase H eligible stream ⊆ H ∪ stream.toFinset := by
  classical
  intro e he
  rcases Finset.mem_union.mp he with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (by simpa [seenUnderfull] using (Finset.mem_filter.mp h).1)

theorem bank_subset_input (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) :
    bankSupport w H eligible stream cuts ⊆ H ∪ stream.toFinset := by
  intro e he
  rcases Finset.mem_union.mp he with hb | hp
  · exact shared_subset_input H eligible stream hb
  · obtain ⟨c,hc,hec⟩ := Finset.mem_biUnion.mp hp
    exact phaseFinal_subset_input w H eligible stream c hec

/-- The returned object is an actual original matching contained in the
input and realizes the optimum of the retained original union. -/
theorem output_spec (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) :
    Matching (outputMatching w H eligible stream cuts) ∧
    outputMatching w H eligible stream cuts ⊆ H ∪ stream.toFinset ∧
    (∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ)) =
      opt (fun e => (w e : ℝ)) (bankSupport w H eligible stream cuts) := by
  exact ⟨decode_matching w _,(decode_subset w _).trans (bank_subset_input w H eligible stream cuts),
    decode_real_weight w _⟩

theorem base_value_le_output (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) :
    opt (fun e => (w e : ℝ)) (sharedBase H eligible stream) ≤
      ∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ) := by
  rw [(output_spec w H eligible stream cuts).2.2,opt_eq_natOpt,opt_eq_natOpt]
  exact_mod_cast natOpt_mono w (shared_subset_bank w H eligible stream cuts)

theorem phase_value_le_output (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (c : ℕ) (hc : c ∈ activeCuts cuts stream) :
    opt (fun e => (w e : ℝ)) (phaseFinal w H eligible stream c) ≤
      ∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ) := by
  rw [(output_spec w H eligible stream cuts).2.2,opt_eq_natOpt,opt_eq_natOpt]
  exact_mod_cast natOpt_mono w (phase_subset_bank w H eligible stream cuts c hc)

/-- Exact shared-store/phase-record counting, valid for every finite prefix. -/
theorem bank_record_cap (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (W : ℕ)
    (hw : ∀ e ∈ H ∪ stream.toFinset, w e ≤ W) :
    bankRecordCount w H eligible stream cuts ≤
      (sharedBase H eligible stream).card + cuts.card * (W * (Fintype.card V / 2)) := by
  unfold bankRecordCount
  apply Nat.add_le_add_left
  calc
    (∑ c ∈ activeCuts cuts stream,
        (phaseFinal w H eligible stream c \ initial H eligible stream c).card)
      ≤ ∑ _c ∈ activeCuts cuts stream, W * (Fintype.card V / 2) := by
        exact Finset.sum_le_sum (fun c _ => phase_owned_record_cap w H eligible stream c W hw)
    _ = (activeCuts cuts stream).card * (W * (Fintype.card V / 2)) := by simp
    _ ≤ cuts.card * (W * (Fintype.card V / 2)) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))

theorem bank_support_card_le_records (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) :
    (bankSupport w H eligible stream cuts).card ≤ bankRecordCount w H eligible stream cuts := by
  let extras := (activeCuts cuts stream).biUnion
    (fun c => phaseFinal w H eligible stream c \ initial H eligible stream c)
  have hs : bankSupport w H eligible stream cuts ⊆ sharedBase H eligible stream ∪ extras := by
    intro e he
    rcases Finset.mem_union.mp he with hb | hp
    · exact Finset.mem_union_left _ hb
    · obtain ⟨c,hc,hec⟩ := Finset.mem_biUnion.mp hp
      by_cases hi : e ∈ initial H eligible stream c
      · exact Finset.mem_union_left _ (initial_subset_shared H eligible stream c hi)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨c,hc,Finset.mem_sdiff.mpr ⟨hec,hi⟩⟩)
  have h1 := Finset.card_le_card hs
  have h2 := Finset.card_union_le (sharedBase H eligible stream) extras
  have h3 := Finset.card_biUnion_le (s := activeCuts cuts stream)
    (t := fun c => phaseFinal w H eligible stream c \ initial H eligible stream c)
  unfold bankRecordCount
  dsimp [extras] at h1 h2
  omega

end RobustMatching.R7WeightedPhaseAssembly
#print axioms RobustMatching.R7WeightedPhaseAssembly.output_spec
#print axioms RobustMatching.R7WeightedPhaseAssembly.bank_record_cap
