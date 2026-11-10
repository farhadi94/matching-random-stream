import RandomOrderMatching.Acquisition.Invariants

noncomputable section
open Classical
namespace RandomOrderMatching.Acquisition
open RandomOrderMatching.Graph
variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- The complete eligible copied records, whether or not a capped execution retains them. -/
def recordsFrom (lower : ℕ) (H : Graph V) (batch : E → List (Edge V)) :
    ℕ → List E → Finset (Edge V × ℕ)
  | _,[] => ∅
  | t,a::as => underfullRecords lower H (batch a) (t+1) ∪
      recordsFrom lower H batch (t+1) as

theorem frozen_step_complete (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (a : E) (hf : s.freezeAt ≠ none) (ha : s.aborted=false)
    (hc : (s.saved ∪ underfullRecords cfg.lower s.ref (batch a) (s.time+1)).card ≤ cfg.uCap) :
    step cfg batch s a={s with time:=s.time+1, saved:=s.saved ∪ underfullRecords cfg.lower s.ref (batch a) (s.time+1)} := by
  simp [step,ha,hf,collectStep,hc]

/-- Sufficient static cap implies exact retention, even though overflow executions clear U. -/
theorem frozen_run_complete (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (as : List E) (hf : s.freezeAt ≠ none) (ha : s.aborted=false)
    (hc : (s.saved ∪ recordsFrom cfg.lower s.ref batch s.time as).card ≤ cfg.uCap) :
    runFrom cfg batch s as={s with time:=s.time+as.length, saved:=s.saved ∪ recordsFrom cfg.lower s.ref batch s.time as} := by
  induction as generalizing s with
  | nil => simp [runFrom,recordsFrom]
  | cons a as ih =>
    have hhead : (s.saved ∪ underfullRecords cfg.lower s.ref (batch a) (s.time+1)).card ≤ cfg.uCap := by
      apply (Finset.card_le_card (show s.saved ∪ underfullRecords cfg.lower s.ref (batch a) (s.time+1) ⊆
        s.saved ∪ recordsFrom cfg.lower s.ref batch s.time (a::as) from ?_)).trans hc
      simp only [recordsFrom]
      intro e he
      rcases Finset.mem_union.mp he with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
    let s' : State V := {s with time:=s.time+1, saved:=s.saved ∪ underfullRecords cfg.lower s.ref (batch a) (s.time+1)}
    have hstep : step cfg batch s a=s' := frozen_step_complete cfg batch s a hf ha hhead
    have hcap : (s'.saved ∪ recordsFrom cfg.lower s'.ref batch s'.time as).card ≤ cfg.uCap := by
      simpa [s',recordsFrom,Finset.union_assoc] using hc
    have hh := ih s' hf ha hcap
    change runFrom cfg batch (step cfg batch s a) as=_
    rw [hstep,hh]
    simp [s',recordsFrom,Finset.union_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem frozen_run_ref (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (as : List E) (hf : s.freezeAt ≠ none) :
    (runFrom cfg batch s as).ref=s.ref := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    have hfreeze : (step cfg batch s a).freezeAt ≠ none := by
      cases hs : s.freezeAt with
      | none => exact (hf hs).elim
      | some t => rw [freeze_persistent cfg batch s a t hs]; simp
    change (runFrom cfg batch (step cfg batch s a) as).ref=_
    rw [ih _ hfreeze]
    simp only [step,hf,ite_false]
    split_ifs
    · rfl
    · exact collectStep_ref cfg s _

end RandomOrderMatching.Acquisition
#print axioms RandomOrderMatching.Acquisition.frozen_run_complete
