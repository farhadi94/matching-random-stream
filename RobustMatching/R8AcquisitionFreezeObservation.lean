import RobustMatching.R8AcquisitionEpochObservation
import RobustMatching.R8AcquisitionCollect
import RobustMatching.R8AcquisitionProbabilityStopping

noncomputable section
open Classical
namespace RobustMatching.R8Acquisition
open RobustMatching.R2Cut RobustMatching.R8AcquisitionProbability
variable {V E : Type*} [Fintype V] [DecidableEq V]

theorem inputPrefix_succ (stream : ℕ → E) (k : ℕ) :
    inputPrefix stream (k+1)=inputPrefix stream k++[stream k] := by
  simp [inputPrefix,List.range_succ]

theorem inputPrefix_add (stream : ℕ → E) (k l : ℕ) :
    inputPrefix stream (k+l)=inputPrefix stream k++inputPrefix (fun i=>stream (k+i)) l := by
  induction l with
  | zero => simp [inputPrefix]
  | succ l ih =>
    rw [Nat.add_succ,inputPrefix_succ,ih,inputPrefix_succ]
    simp [List.append_assoc]

theorem stateAt_add (cfg : Config) (batch : E → List (Edge V)) (stream : ℕ → E) (k l : ℕ) :
    stateAt cfg batch stream (k+l)=runFrom cfg batch (stateAt cfg batch stream k)
      (inputPrefix (fun i=>stream (k+i)) l) := by
  simp only [stateAt,inputPrefix_add,run,runFrom_append]

theorem stateAt_before_freeze (cfg : Config) (batch : E → List (Edge V))
    (stream : ℕ → E) (i k tau : ℕ) (hi : i<tau) (hik : i≤k)
    (ht : (stateAt cfg batch stream k).freezeAt=some tau) :
    (stateAt cfg batch stream i).freezeAt=none := by
  cases hs : (stateAt cfg batch stream i).freezeAt with
  | none => rfl
  | some u =>
    have hv := actual_freeze_valid cfg batch stream i u hs
    have hh := actual_freeze_persists cfg batch stream i k u hik hs
    rw [ht] at hh
    have := Option.some.inj hh
    omega

theorem first_freeze_epoch (cfg : Config) (batch : E → List (Edge V))
    (stream : ℕ → E) (k tau : ℕ) (ht : (stateAt cfg batch stream k).freezeAt=some tau) :
    ∃ j, tau=(j+1)*cfg.epochLength ∧ j<operationBound (V:=V) cfg.beta := by
  have hv := actual_freeze_valid cfg batch stream k tau ht
  have hpred : tau-1<tau := by omega
  have hbefore := stateAt_before_freeze cfg batch stream (tau-1) k tau hpred (by omega) ht
  have hnow := actual_freeze_restrict cfg batch stream tau k tau hv.2 le_rfl ht
  have hp := ((run_invariant cfg batch (inputPrefix stream (tau-1))).1 hbefore).2
  have ha := ((run_invariant cfg batch (inputPrefix stream (tau-1))).1 hbefore).1
  let s := stateAt cfg batch stream (tau-1)
  have hnext : (step cfg batch s (stream (tau-1))).freezeAt=some tau := by
    rw [←stateAt_succ]
    simpa [Nat.sub_add_cancel (show 1≤tau by omega)] using hnow
  have htime : s.time=tau-1 := stateAt_time cfg batch stream (tau-1)
  have hclock := hp.2.1
  change s.time=s.epochs*cfg.epochLength+s.pos at hclock
  change s.aborted=false at ha
  change s.freezeAt=none at hbefore
  have hend : s.pos+1=cfg.epochLength := by
    simp only [step,ha,hbefore,Bool.false_eq_true,ite_false,ite_true,acquireStep] at hnext
    split_ifs at hnext with he hd
    · exact he
  refine ⟨s.epochs,?_,?_⟩
  · rw [Nat.add_mul,Nat.one_mul]
    omega
  · have hb := epoch_count_bound cfg s hp
    unfold operationBound
    omega

theorem stateAt_boundary_pos (cfg : Config) (batch : E → List (Edge V))
    (stream : ℕ → E) (j : ℕ)
    (hf : (stateAt cfg batch stream (j*cfg.epochLength)).freezeAt=none) :
    (stateAt cfg batch stream (j*cfg.epochLength)).pos=0 := by
  have hp := ((run_invariant cfg batch (inputPrefix stream (j*cfg.epochLength))).1 hf).2
  change EpochProgress cfg (stateAt cfg batch stream (j*cfg.epochLength)) at hp
  have hh := congrArg (fun t=>t%cfg.epochLength) hp.2.1
  rw [stateAt_time] at hh
  simpa [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hp.1] using hh.symm

/-- Actual freeze identifies one of the deterministic epochs and an unchanged
reference that found no insertable copied edge in that epoch. -/
theorem actual_empty_epoch (cfg : Config) (batch : E → List (Edge V))
    (stream : ℕ → E) (k tau : ℕ) (ht : (stateAt cfg batch stream k).freezeAt=some tau) :
    ∃ j, j<operationBound (V:=V) cfg.beta ∧ tau=(j+1)*cfg.epochLength ∧
      (stateAt cfg batch stream k).ref=(stateAt cfg batch stream (j*cfg.epochLength)).ref ∧
      ∀ i<cfg.epochLength,∀ e∈batch (stream (j*cfg.epochLength+i)),
        ¬insertable cfg.lower (stateAt cfg batch stream (j*cfg.epochLength)).ref e := by
  obtain ⟨j,htau,hj⟩ := first_freeze_epoch cfg batch stream k tau ht
  have hv := actual_freeze_valid cfg batch stream k tau ht
  have hstart : j*cfg.epochLength<tau := by rw [htau,Nat.add_mul,Nat.one_mul]; have := cfg.epoch_pos; omega
  have hf := stateAt_before_freeze cfg batch stream (j*cfg.epochLength) k tau hstart (by omega) ht
  have ha := ((run_invariant cfg batch (inputPrefix stream (j*cfg.epochLength))).1 hf).1
  have hp := stateAt_boundary_pos cfg batch stream j hf
  have hnow := actual_freeze_restrict cfg batch stream tau k tau hv.2 le_rfl ht
  let block := inputPrefix (fun i=>stream (j*cfg.epochLength+i)) cfg.epochLength
  have hblock : block.length=cfg.epochLength := by simp [block,inputPrefix]
  have hdecomp : stateAt cfg batch stream tau=runFrom cfg batch
      (stateAt cfg batch stream (j*cfg.epochLength)) block := by
    rw [htau,Nat.add_mul,Nat.one_mul,stateAt_add]
  have hnon : (runFrom cfg batch (stateAt cfg batch stream (j*cfg.epochLength)) block).freezeAt≠none := by
    rw [←hdecomp,hnow]; simp
  have he := empty_epoch_observation cfg batch _ block hf ha hp hblock hnon
  have hfinal : (stateAt cfg batch stream k).ref=(stateAt cfg batch stream tau).ref := by
    have hk : k=tau+(k-tau) := by omega
    rw [hk,stateAt_add]
    exact frozen_run_ref cfg batch _ _ (by rw [hnow]; simp)
  refine ⟨j,hj,htau,hfinal.trans (by rw [hdecomp]; exact he.1),?_⟩
  intro i hi e hee
  apply he.2 _ ?_ e hee
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩


theorem step_acquiring_store (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (a : E) (hf : s.freezeAt=none) (ha : s.aborted=false) :
    (step cfg batch s a).saved=s.saved ∧ (step cfg batch s a).aborted=false := by
  simp only [step,hf,ha,Bool.false_eq_true,ite_false,ite_true,acquireStep]
  split_ifs <;> exact ⟨rfl,rfl⟩

theorem stateAt_unfrozen_saved (cfg : Config) (batch : E → List (Edge V))
    (stream : ℕ → E) (k : ℕ) (hf : (stateAt cfg batch stream k).freezeAt=none) :
    (stateAt cfg batch stream k).saved=∅ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hprev : (stateAt cfg batch stream k).freezeAt=none := by
      cases hs : (stateAt cfg batch stream k).freezeAt with
      | none => rfl
      | some t =>
        have hh := freeze_persistent cfg batch (stateAt cfg batch stream k) (stream k) t hs
        rw [←stateAt_succ,hf] at hh
        cases hh
    have ha := ((run_invariant cfg batch (inputPrefix stream k)).1 hprev).1
    rw [stateAt_succ,(step_acquiring_store cfg batch _ _ hprev ha).1]
    exact ih hprev

/-- At the freeze itself no suffix record has yet been collected and no abort has occurred. -/
theorem actual_freeze_state_clean (cfg : Config) (batch : E → List (Edge V))
    (stream : ℕ → E) (k tau : ℕ) (ht : (stateAt cfg batch stream k).freezeAt=some tau) :
    (stateAt cfg batch stream tau).saved=∅ ∧ (stateAt cfg batch stream tau).aborted=false := by
  have hv := actual_freeze_valid cfg batch stream k tau ht
  have hf := stateAt_before_freeze cfg batch stream (tau-1) k tau (by omega) (by omega) ht
  have ha := ((run_invariant cfg batch (inputPrefix stream (tau-1))).1 hf).1
  have hs := stateAt_unfrozen_saved cfg batch stream (tau-1) hf
  have hh := step_acquiring_store cfg batch (stateAt cfg batch stream (tau-1)) (stream (tau-1)) hf ha
  rw [←stateAt_succ,Nat.sub_add_cancel (show 1≤tau by omega),hs] at hh
  exact hh

end RobustMatching.R8Acquisition
#print axioms RobustMatching.R8Acquisition.actual_empty_epoch
