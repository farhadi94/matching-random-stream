import RandomOrderMatching.Resources.TotalRecords
import RandomOrderMatching.Weights.Windows.LiveCount

noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Resources
open RandomOrderMatching.Graph RandomOrderMatching.Streaming RandomOrderMatching.Weights.Windows
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

def dictionaryRecords (p : Parameters) (a : Machine V) (record : a.State → ℕ)
    (w : Edge V → ℚ) (n : ℕ) (stream : ℕ → Edge V) (t : ℕ) : ℕ :=
  ∑ j ∈ p.dictionary w n stream t, record (p.retained a w n stream t j)

/-- Actual retained states are complete filtered runs, so the hard local cap
applies even to adaptively retired dictionaries without conditioning on survival. -/
theorem dictionary_records_cap (p : Parameters) (a : Machine V) (record : a.State → ℕ)
    (w : Edge V → ℚ) (n : ℕ) (stream : ℕ → Edge V) (t h R : ℕ)
    (hw : ∀ e, 0 < w e)
    (hscale : (p.B : ℝ)^(-(h:ℤ)) ≤ (p.eta:ℝ)/n)
    (hlocal : ∀ j, record (a.run (p.integerWeight w j)
      (p.localList w j (streamList stream t))) ≤ R) :
    dictionaryRecords p a record w n stream t ≤ (p.k+h+1)*R := by
  unfold dictionaryRecords
  calc
    _ ≤ ∑ _j ∈ p.dictionary w n stream t, R := by
      apply Finset.sum_le_sum
      intro j hj
      rw [p.dictionary_state_eq_filtered a w n stream t j hj]
      exact hlocal j
    _ = (p.dictionary w n stream t).card*R := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (p.dictionary_count w n stream hw h hscale t)

/-- The window compiler's local machine is exactly the complete bounded-
integer wrapper. The copy graph/model may depend on the integer edge weights;
the finite copied vertex alphabet and all capacities are fixed in advance. -/
def boundedMachine (beta lower LU L0 kappa : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (models : (Edge V → ℕ) → RandomOrderMatching.Acquisition.BatchModel (Edge V) C) : Machine V where
  State := OuterState V (LocalState (RandomOrderMatching.Acquisition.State C) V) (Fintype.card V)
    (acquisitionBudget (Fintype.card C) beta)
  initial _ := outerInit _ _ (fun _ => acquiredLocalInit)
  step w := outerStep _ _
    (fullCapacity (Fintype.card V) (acquisitionBudget (Fintype.card C) beta) kappa L0)
    (fun M => acquiredLocalStep w
      (configForScale beta lower
        (copiedCapacity (acquisitionBudget (Fintype.card C) beta) kappa LU)
        (acquisitionBudget (Fintype.card C) beta) M hb hl) (models w))
  output w := outerOutput _ _ w (fun _ => localAnswer w)

theorem boundedMachine_run (beta lower LU L0 kappa : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (models : (Edge V → ℕ) → RandomOrderMatching.Acquisition.BatchModel (Edge V) C)
    (w : Edge V → ℕ) (l : List (Edge V)) :
    (boundedMachine beta lower LU L0 kappa hb hl models).run w l =
      boundedIntegerRun (Fintype.card V) (acquisitionBudget (Fintype.card C) beta)
        (fullCapacity (Fintype.card V) (acquisitionBudget (Fintype.card C) beta) kappa L0)
        w (fun M => configForScale beta lower
          (copiedCapacity (acquisitionBudget (Fintype.card C) beta) kappa LU)
          (acquisitionBudget (Fintype.card C) beta) M hb hl) (models w) l := rfl

theorem boundedMachine_records (beta lower LU L0 kappa W : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (models : (Edge V → ℕ) → RandomOrderMatching.Acquisition.BatchModel (Edge V) C)
    (w : Edge V → ℕ) (l : List (Edge V))
    (hnd : l.Nodup) (hw : ∀ e ∈ l, w e ≤ W) :
    outerRecordCount (Fintype.card V) (acquisitionBudget (Fintype.card C) beta) localRecords
      ((boundedMachine beta lower LU L0 kappa hb hl models).run w l) ≤
      configuredRecordBound (Fintype.card V) (Fintype.card C) beta kappa LU L0 W := by
  rw [boundedMachine_run]
  exact bounded_integer_records _ _ _ w _ (models w) l beta _ W _ rfl
    (fun _ => rfl) (fun _ => rfl) hw (stream_length_le_square l hnd)

/-- Fully instantiated hard record count for the actual dictionary of complete
bounded-integer executions. This has no local space oracle as a premise. -/
theorem actual_window_records (p : Parameters) (beta lower LU L0 kappa : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (models : (Edge V → ℕ) → RandomOrderMatching.Acquisition.BatchModel (Edge V) C)
    (w : Edge V → ℚ) (stream : ℕ → Edge V) (t h : ℕ)
    (hw : ∀ e, 0 < w e) (hnd : (streamList stream t).Nodup)
    (hscale : (p.B : ℝ)^(-(h:ℤ)) ≤ (p.eta:ℝ)/Fintype.card V) :
    dictionaryRecords p (boundedMachine beta lower LU L0 kappa hb hl models)
      (outerRecordCount (Fintype.card V) (acquisitionBudget (Fintype.card C) beta) localRecords)
      w (Fintype.card V) stream t ≤
      (p.k+h+1) * configuredRecordBound (Fintype.card V) (Fintype.card C)
        beta kappa LU L0 p.integerRange := by
  apply dictionary_records_cap p _ _ w (Fintype.card V) stream t h _ hw hscale
  intro j
  apply boundedMachine_records
  · exact hnd.filter _
  · intro e he
    have hh := (List.mem_filter.mp he).2
    have hc : p.contains j (w e) := by simpa [Parameters.belongs] using hh
    exact (p.normalized_range hc).2

/-- The logarithmic live-window multiplier is instantiated, not an assumed
bound on a user-supplied dictionary. -/
theorem actual_window_records_log (p : Parameters) (beta lower LU L0 kappa : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (models : (Edge V → ℕ) → RandomOrderMatching.Acquisition.BatchModel (Edge V) C)
    (w : Edge V → ℚ) (stream : ℕ → Edge V) (t : ℕ)
    (hw : ∀ e, 0 < w e) (hnd : (streamList stream t).Nodup)
    (hn : 0 < Fintype.card V) :
    dictionaryRecords p (boundedMachine beta lower LU L0 kappa hb hl models)
      (outerRecordCount (Fintype.card V) (acquisitionBudget (Fintype.card C) beta) localRecords)
      w (Fintype.card V) stream t ≤
      (p.k+p.liveExponent (Fintype.card V)+1) *
        configuredRecordBound (Fintype.card V) (Fintype.card C)
          beta kappa LU L0 p.integerRange :=
  actual_window_records p beta lower LU L0 kappa hb hl models w stream t
    (p.liveExponent (Fintype.card V)) hw hnd (p.liveExponent_spec (Fintype.card V) hn)

end RandomOrderMatching.Resources
