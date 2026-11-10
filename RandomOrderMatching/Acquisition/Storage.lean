import RandomOrderMatching.Acquisition.Provenance
import RandomOrderMatching.Acquisition.Termination

noncomputable section
open Classical
namespace RandomOrderMatching.Acquisition
open RandomOrderMatching.Graph
variable {V E : Type*} [Fintype V] [DecidableEq V]

theorem cleanupFuel_card (beta fuel : ℕ) (H : Graph V) :
    (cleanupFuel beta fuel H).card≤H.card := Finset.card_le_card (cleanupFuel_subset beta fuel H)

/-- Every transient deletion-cleanup graph after an insertion obeys this peak bound. -/
theorem insert_cleanup_peak (beta fuel : ℕ) (H : Graph V) (e : Edge V)
    (hH : Upper beta H) :
    2*(cleanupFuel beta fuel (insert e H)).card≤Fintype.card V*beta+2 := by
  have h1 := cleanupFuel_card beta fuel (insert e H)
  have h2 := Finset.card_insert_le e H
  have h3 := upper_edge_count beta hH
  omega

theorem step_pos_bound (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (hs : s.pos<cfg.epochLength) (a : E) :
    (step cfg batch s a).pos<cfg.epochLength := by
  simp only [step,acquireStep,collectStep]
  split_ifs <;> simp_all only
  all_goals first | exact cfg.epoch_pos | exact hs | omega

theorem runFrom_pos_bound (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (hs : s.pos<cfg.epochLength) (as : List E) :
    (runFrom cfg batch s as).pos<cfg.epochLength := by
  induction as generalizing s with
  | nil => exact hs
  | cons a as ih => exact ih _ (step_pos_bound cfg batch s hs a)

theorem run_pos_bound (cfg : Config) (batch : E → List (Edge V)) (as : List E) :
    (run cfg batch as).pos<cfg.epochLength :=
  runFrom_pos_bound cfg batch initialState cfg.epoch_pos as

def ValidStamps (s : State V) : Prop := ∀ z∈s.saved,0<z.2 ∧ z.2 ≤ s.time

theorem underfullRecords_stamp (lower : ℕ) (H : Graph V) (es : List (Edge V)) (t : ℕ)
    {z : Edge V × ℕ} (hz : z∈underfullRecords lower H es t) : z.2=t := by
  obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hz
  exact congrArg Prod.snd heq.symm

theorem collectStep_stamps (cfg : Config) (s : State V) (hs : ValidStamps s)
    (es : List (Edge V)) : ValidStamps (collectStep cfg s es) := by
  simp only [collectStep]
  split_ifs with hc
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have hh := hs z hz
      exact ⟨hh.1,by change z.2 ≤ s.time+1; omega⟩
    · have hh := underfullRecords_stamp cfg.lower s.ref es (s.time+1) hz
      exact ⟨by omega,by change z.2 ≤ s.time+1; omega⟩
  · intro z hz
    exact (Finset.notMem_empty z hz).elim

theorem step_stamps (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (hs : ValidStamps s) (a : E) : ValidStamps (step cfg batch s a) := by
  simp only [step]
  split_ifs
  · intro z hz
    have hh := hs z hz
    exact ⟨hh.1,by change z.2 ≤ s.time+1; omega⟩
  · simp only [acquireStep]
    split_ifs <;> intro z hz <;> have hh := hs z hz <;>
      exact ⟨hh.1,by change z.2 ≤ s.time+1; omega⟩
  · exact collectStep_stamps cfg s hs _

theorem runFrom_stamps (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (hs : ValidStamps s) (as : List E) : ValidStamps (runFrom cfg batch s as) := by
  induction as generalizing s with
  | nil => exact hs
  | cons a as ih => exact ih _ (step_stamps cfg batch s hs a)

theorem run_stamps (cfg : Config) (batch : E → List (Edge V)) (as : List E) :
    ValidStamps (run cfg batch as) :=
  runFrom_stamps cfg batch initialState (by simp [ValidStamps,initialState]) as

theorem run_epoch_counter (cfg : Config) (batch : E → List (Edge V)) (as : List E) :
    (run cfg batch as).epochs≤Fintype.card V*cfg.beta^2 := by
  induction as using List.reverseRecOn with
  | nil => simp [run,runFrom,initialState]
  | append_singleton as a ih =>
    let s := run cfg batch as
    change s.epochs≤Fintype.card V*cfg.beta^2 at ih
    have heq : run cfg batch (as++[a])=step cfg batch s a := by simp [run,runFrom,List.foldl_append,s]
    rw [heq]
    by_cases hn : (step cfg batch s a).freezeAt=none
    · exact epoch_count_bound cfg _ ((step_invariant cfg batch s (run_invariant cfg batch as) a).1 hn).2
    · cases hf : s.freezeAt with
      | some t =>
        simp only [step,hf,Option.some_ne_none,ite_false,collectStep]
        split_ifs <;> exact ih
      | none =>
        have ha := ((run_invariant cfg batch as).1 hf).1
        change s.aborted=false at ha
        simp only [step,ha,hf,Bool.false_eq_true,ite_false,ite_true,acquireStep] at hn ⊢
        split_ifs at hn ⊢ <;> simp_all

end RandomOrderMatching.Acquisition
#print axioms RandomOrderMatching.Acquisition.insert_cleanup_peak
#print axioms RandomOrderMatching.Acquisition.run_stamps
#print axioms RandomOrderMatching.Acquisition.run_epoch_counter
