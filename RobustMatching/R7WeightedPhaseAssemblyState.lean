import RobustMatching.R7CopyDualHistorical
import RobustMatching.R7CopyDualLifting

/-! Concrete original-label phase execution and its causal initial graph.
The underfull predicate is a fixed classifier from the acquired reference;
only labels already seen are included in a phase's initial parent support. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7WeightedPhaseAssembly
set_option linter.unusedSectionVars false
open RobustMatching.R2Cut RobustMatching.R7WeightedPhase
open RobustMatching.R6FableImportance RobustMatching.R7CopyDualHistorical
variable {V : Type*} [Fintype V] [DecidableEq V]

def seenUnderfull (eligible : Edge V → Prop) (stream : List (Edge V)) (t : ℕ) : Graph V := by
  classical
  exact (stream.take t).toFinset.filter eligible

def initial (H : Graph V) (eligible : Edge V → Prop) (stream : List (Edge V)) (c : ℕ) : Graph V :=
  H ∪ seenUnderfull eligible stream c

def phaseHost (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c t : ℕ) : Graph V :=
  run w ∅ (initial H eligible stream c) ((stream.drop c).take t)

def phaseFinal (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) : Graph V :=
  run w ∅ (initial H eligible stream c) (stream.drop c)

def sharedBase (H : Graph V) (eligible : Edge V → Prop) (stream : List (Edge V)) : Graph V :=
  H ∪ seenUnderfull eligible stream stream.length

theorem run_append (w : Edge V → ℕ) (forced G : Graph V) (a b : List (Edge V)) :
    run w forced G (a ++ b) = run w forced (run w forced G a) b := by
  simp [run, List.foldl_append]

theorem run_prefix_mono (w : Edge V → ℕ) (forced G : Graph V)
    (stream : List (Edge V)) {i j : ℕ} (hij : i ≤ j) :
    run w forced G (stream.take i) ⊆ run w forced G (stream.take j) := by
  have hj : j = i + (j-i) := by omega
  rw [hj, List.take_add, run_append]
  exact subset_run w forced _ _

theorem phaseHost_zero (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) : phaseHost w H eligible stream c 0 = initial H eligible stream c := by
  simp [phaseHost, run]

theorem phaseHost_terminal (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) :
    phaseHost w H eligible stream c (stream.drop c).length = phaseFinal w H eligible stream c := by
  unfold phaseHost phaseFinal
  rw [List.take_length]

theorem phaseHost_step (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c i : ℕ) (hi : i < (stream.drop c).length) :
    phaseHost w H eligible stream c (i+1) =
      step w ∅ (phaseHost w H eligible stream c i) ((stream.drop c)[i]) := by
  unfold phaseHost
  rw [List.take_succ_eq_append_getElem hi, run_append]
  rfl

theorem phaseHost_mono (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) {i j : ℕ} (hij : i ≤ j) :
    phaseHost w H eligible stream c i ⊆ phaseHost w H eligible stream c j :=
  run_prefix_mono w ∅ _ _ hij

theorem seenUnderfull_mono (eligible : Edge V → Prop) (stream : List (Edge V))
    {a c : ℕ} (hac : a ≤ c) : seenUnderfull eligible stream a ⊆ seenUnderfull eligible stream c := by
  classical
  intro e he
  obtain ⟨hm,hel⟩ := Finset.mem_filter.mp he
  apply Finset.mem_filter.mpr
  refine ⟨?_,hel⟩
  apply List.mem_toFinset.mpr
  have hh : e ∈ (stream.take c).take a := by
    simpa only [List.take_take,Nat.min_eq_left hac] using List.mem_toFinset.mp hm
  exact List.take_subset a (stream.take c) hh

theorem early_base_subset_initial (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) {a c : ℕ} (hac : a ≤ c) :
    initial H eligible stream a ⊆ initial H eligible stream c := by
  exact Finset.union_subset_union (Finset.Subset.refl _) (seenUnderfull_mono eligible stream hac)

theorem early_support_in_phase (w : Edge V → ℕ) (H A : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) {a c : ℕ} (hac : a ≤ c)
    (hA : A ⊆ initial H eligible stream a) (t : ℕ) :
    A ⊆ phaseHost w H eligible stream c t := by
  exact (hA.trans (early_base_subset_initial H eligible stream hac)).trans
    (subset_run w ∅ _ _)

theorem initial_subset_shared (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) : initial H eligible stream c ⊆ sharedBase H eligible stream := by
  classical
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact Finset.mem_union_left _ he
  · obtain ⟨hmem,hel⟩ := Finset.mem_filter.mp he
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨?_,hel⟩
    simp only [List.take_length,List.mem_toFinset]
    exact List.take_subset c stream (List.mem_toFinset.mp hmem)

theorem initial_subset_input (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) : initial H eligible stream c ⊆ H ∪ stream.toFinset := by
  classical
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact Finset.mem_union_left _ he
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.take_subset c stream (List.mem_toFinset.mp (Finset.mem_filter.mp he).1)))

theorem phaseFinal_subset_input (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) : phaseFinal w H eligible stream c ⊆ H ∪ stream.toFinset := by
  intro e he
  rcases Finset.mem_union.mp (run_subset w ∅ _ _ he) with hi | ht
  · exact initial_subset_input H eligible stream c hi
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.drop_subset c stream (List.mem_toFinset.mp ht)))

/-- No unexposed original outside H can enter the initial host. -/
theorem initial_mem_iff (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) (e : Edge V) :
    e ∈ initial H eligible stream c ↔ e ∈ H ∨ e ∈ stream.take c ∧ eligible e := by
  classical
  simp [initial, seenUnderfull]

theorem take_drop_membership (stream : List (Edge V)) (c : ℕ) (e : Edge V) :
    e ∈ stream ↔ e ∈ stream.take c ∨ e ∈ stream.drop c := by
  rw [← List.mem_append, List.take_append_drop]

theorem drop_membership_mono (stream : List (Edge V)) {c t : ℕ} (hct : c ≤ t)
    (e : Edge V) (he : e ∈ stream.drop t) : e ∈ stream.drop c := by
  have ht : t = c + (t-c) := by omega
  rw [ht, ← List.drop_drop] at he
  exact List.drop_subset (t-c) (stream.drop c) he

/-- Every shared underfull label is initially present or later tested. -/
theorem shared_initial_or_tested (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) (e : Edge V) (he : e ∈ sharedBase H eligible stream) :
    e ∈ initial H eligible stream c ∨ e ∈ stream.drop c := by
  classical
  rcases Finset.mem_union.mp he with he | he
  · exact Or.inl (Finset.mem_union_left _ he)
  · obtain ⟨hmem,hel⟩ := Finset.mem_filter.mp he
    have hlist : e ∈ stream := by simpa using hmem
    rcases (take_drop_membership stream c e).mp hlist with hp | hs
    · exact Or.inl ((initial_mem_iff H eligible stream c e).mpr (Or.inr ⟨hp,hel⟩))
    · exact Or.inr hs

/-- This exactly covers H gates, all U gates/internal U labels, and later
roots/missing/internal labels. No matching or copy-role assumption is needed. -/
theorem repair_parent_initial_or_tested (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) {c t : ℕ} (hct : c ≤ t) (e : Edge V)
    (he : e ∈ sharedBase H eligible stream ∨ e ∈ stream.drop t) :
    e ∈ initial H eligible stream c ∨ e ∈ stream.drop c := by
  rcases he with hs | hl
  · exact shared_initial_or_tested H eligible stream c e hs
  · exact Or.inr (drop_membership_mono stream hct e hl)

/-- A historical closure host exists for every actually initial/tested
original. It may cease to be closed at subsequent times. -/
theorem phase_historical_closure (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) (e : Edge V)
    (he : e ∈ initial H eligible stream c ∨ e ∈ stream.drop c) :
    ∃ t ≤ (stream.drop c).length,
      opt (fun f => (w f : ℝ)) (insert e (phaseHost w H eligible stream c t)) =
        opt (fun f => (w f : ℝ)) (phaseHost w H eligible stream c t) := by
  rcases he with hi | ht
  · refine ⟨0,Nat.zero_le _,?_⟩
    rw [phaseHost_zero,Finset.insert_eq_of_mem hi]
  · obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp ht
    refine ⟨i+1,by omega,?_⟩
    rw [phaseHost_step w H eligible stream c i hi,←hval]
    exact phase_step_closed w ∅ _ _

/-- Voluntary new records are bounded on every concrete prefix. -/
theorem run_extra_record_bound (w : Edge V → ℕ) (G : Graph V)
    (stream : List (Edge V)) :
    (run w ∅ G stream \ G).card + natOpt w G ≤ natOpt w (run w ∅ G stream) := by
  have hr := run_record_bound w ∅ G stream
  simp only [Finset.sdiff_empty] at hr
  have hc := Finset.card_sdiff_add_card_eq_card (subset_run w ∅ G stream)
  omega

theorem phase_extra_cap (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c W : ℕ)
    (hw : ∀ e ∈ H ∪ stream.toFinset, w e ≤ W) :
    (phaseFinal w H eligible stream c \ sharedBase H eligible stream).card ≤
      W * (Fintype.card V / 2) := by
  have hs := phaseFinal_subset_input w H eligible stream c
  have hb := natOpt_vertex_bound w (phaseFinal w H eligible stream c) Finset.univ W
    (fun e he => hw e (hs he)) (fun _ _ => Finset.subset_univ _)
  have hr := run_extra_record_bound w (initial H eligible stream c) (stream.drop c)
  have hc : (phaseFinal w H eligible stream c \ sharedBase H eligible stream).card ≤
      (phaseFinal w H eligible stream c \ initial H eligible stream c).card := by
    apply Finset.card_le_card
    intro e he
    obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp he
    exact Finset.mem_sdiff.mpr ⟨hp,fun hi => hn (initial_subset_shared H eligible stream c hi)⟩
  change (phaseFinal w H eligible stream c \ initial H eligible stream c).card +
    natOpt w (initial H eligible stream c) ≤ natOpt w (phaseFinal w H eligible stream c) at hr
  simp only [Finset.card_univ] at hb
  omega


/-- This counts per-phase owned records even if an accepted parent later
also enters the shared underfull store. Initial graphs are shared views. -/
theorem phase_owned_record_cap (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c W : ℕ)
    (hw : ∀ e ∈ H ∪ stream.toFinset, w e ≤ W) :
    (phaseFinal w H eligible stream c \ initial H eligible stream c).card ≤
      W * (Fintype.card V / 2) := by
  have hs := phaseFinal_subset_input w H eligible stream c
  have hb := natOpt_vertex_bound w (phaseFinal w H eligible stream c) Finset.univ W
    (fun e he => hw e (hs he)) (fun _ _ => Finset.subset_univ _)
  have hr := run_extra_record_bound w (initial H eligible stream c) (stream.drop c)
  change (phaseFinal w H eligible stream c \ initial H eligible stream c).card +
    natOpt w (initial H eligible stream c) ≤ natOpt w (phaseFinal w H eligible stream c) at hr
  simp only [Finset.card_univ] at hb
  omega

end RobustMatching.R7WeightedPhaseAssembly
#print axioms RobustMatching.R7WeightedPhaseAssembly.phase_historical_closure
#print axioms RobustMatching.R7WeightedPhaseAssembly.phase_extra_cap
