import RandomOrderMatching.Resources.LocalState
import RandomOrderMatching.Acquisition.Storage

noncomputable section
namespace RandomOrderMatching.Resources
open RandomOrderMatching.Graph RandomOrderMatching.Streaming
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

theorem run_freeze_timestamp (cfg : RandomOrderMatching.Acquisition.Config)
    (batch : E → List (Edge C)) (l : List E) (tau : ℕ)
    (hf : (RandomOrderMatching.Acquisition.run cfg batch l).freezeAt = some tau) : tau ≤ l.length := by
  have hvalid : ∀ tau, (RandomOrderMatching.Acquisition.run cfg batch l).freezeAt = some tau →
      0 < tau ∧ tau ≤ (RandomOrderMatching.Acquisition.run cfg batch l).time := by
    clear hf tau
    induction l using List.reverseRecOn with
    | nil => simp [RandomOrderMatching.Acquisition.run,RandomOrderMatching.Acquisition.runFrom,RandomOrderMatching.Acquisition.initialState]
    | append_singleton l e ih =>
      have heq : RandomOrderMatching.Acquisition.run cfg batch (l++[e]) =
          RandomOrderMatching.Acquisition.step cfg batch (RandomOrderMatching.Acquisition.run cfg batch l) e := by
        simp [RandomOrderMatching.Acquisition.run,RandomOrderMatching.Acquisition.runFrom,List.foldl_append]
      rw [heq]
      exact RandomOrderMatching.Acquisition.step_freeze_valid cfg batch _ ih e
  simpa only [RandomOrderMatching.Acquisition.run_time] using (hvalid tau hf).2

theorem scale_label_bound (n Q M : ℕ) (hM : M ∈ scales n Q) : M ≤ n*n+1 := by
  obtain ⟨himage,_⟩ := Finset.mem_filter.mp hM
  obtain ⟨j,hjmem,rfl⟩ := Finset.mem_image.mp himage
  have hj' : j ≤ Nat.log 2 (n*n) := by simpa using Finset.mem_range.mp hjmem
  have hp := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hj'
  by_cases hz : n*n=0
  · simpa [hz] using hp
  · exact hp.trans ((Nat.pow_log_le_self 2 hz).trans (Nat.le_succ _))

theorem configured_epoch_bound (n Q M beta lower uCap : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta) (hM : M ∈ scales n Q) :
    (configForScale beta lower uCap Q M hb hl).epochLength ≤ n*n+1 := by
  apply max_le (by omega)
  exact (Nat.div_le_self M _).trans (scale_label_bound n Q M hM)

def counterMax (n N beta W R : ℕ) : ℕ :=
  n*n + N*beta^2 + n*W + R + 1

/-- Actual acquisition integers have bounded binary encodings. The bound is
independent of the total weight magnitude outside the bounded-integer window. -/
theorem configured_acquisition_counters (beta lower uCap Q M W R : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (l : List (Edge V))
    (hnd : l.Nodup) (hM : M ∈ scales (Fintype.card V) Q) :
    let cfg := configForScale beta lower uCap Q M hb hl
    let a := RandomOrderMatching.Acquisition.run cfg model.copies l
    let K := counterMax (Fintype.card V) (Fintype.card C) beta W R
    a.time ≤ K ∧ a.pos ≤ K ∧ a.epochs ≤ K ∧
      (∀ tau, a.freezeAt=some tau → tau ≤ K) ∧
      (∀ z∈a.saved, z.2 ≤ K) := by
  dsimp only
  let cfg := configForScale beta lower uCap Q M hb hl
  have ht := RandomOrderMatching.Acquisition.run_time cfg model.copies l
  have hp := RandomOrderMatching.Acquisition.run_pos_bound cfg model.copies l
  have he := RandomOrderMatching.Acquisition.run_epoch_counter cfg model.copies l
  have hs := RandomOrderMatching.Acquisition.run_stamps cfg model.copies l
  have hm := stream_length_le_square l hnd
  have hc := configured_epoch_bound (Fintype.card V) Q M beta lower uCap hb hl hM
  change cfg.epochLength ≤ _ at hc
  change _ ≤ Fintype.card C * beta^2 at he
  dsimp only [cfg] at ht hp he hs hc
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold counterMax; omega
  · unfold counterMax; omega
  · unfold counterMax; omega
  · intro tau hf
    have hh := run_freeze_timestamp cfg model.copies l tau hf
    unfold counterMax; omega
  · intro z hz
    have hh := (hs z hz).2
    unfold counterMax; omega

/-- A conservative transition ledger permits both old and new stores plus a
whole incoming copied batch. This is separate from oracle working memory. -/
theorem two_state_transition_cap {old new R kappa scratch : ℕ}
    (ho : old ≤ R) (hn : new ≤ R) (hs : scratch ≤ kappa) :
    old + new + scratch ≤ 2*R+kappa := by omega

end RandomOrderMatching.Resources
