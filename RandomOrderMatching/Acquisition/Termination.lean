import RandomOrderMatching.Acquisition.Invariants

noncomputable section
open Classical
namespace RandomOrderMatching.Acquisition
open RandomOrderMatching.Graph
variable {V E : Type*} [Fintype V] [DecidableEq V]

def dirtyCost (b : Bool) : ℤ := if b then 1 else 0

def EpochProgress (cfg : Config) (s : State V) : Prop :=
  s.pos < cfg.epochLength ∧ s.time=s.epochs*cfg.epochLength+s.pos ∧
  (s.epochs:ℤ)+dirtyCost s.dirty ≤ potential cfg.beta s.ref

theorem dirtyCost_nonneg (b : Bool) : 0 ≤ dirtyCost b := by cases b <;> decide

theorem dirtyCost_or (a b : Bool) : dirtyCost (a || b) ≤ dirtyCost a+dirtyCost b := by
  cases a <;> cases b <;> decide

theorem acquireStep_progress (cfg : Config) (s : State V) (es : List (Edge V))
    (hp : EpochProgress cfg s) (hf : s.freezeAt=none) :
    (acquireStep cfg s es).freezeAt=none → EpochProgress cfg (acquireStep cfg s es) := by
  rcases hp with ⟨hpos,htime,hpot⟩
  have hu := batchUpdate_progress cfg.beta cfg.lower cfg.lower_gap s.ref es
  change potential cfg.beta s.ref+dirtyCost (batchUpdate cfg.beta cfg.lower s.ref es).2 ≤
    potential cfg.beta (batchUpdate cfg.beta cfg.lower s.ref es).1 at hu
  have hsum : (s.epochs:ℤ)+dirtyCost (s.dirty || (batchUpdate cfg.beta cfg.lower s.ref es).2) ≤
      potential cfg.beta (batchUpdate cfg.beta cfg.lower s.ref es).1 := by
    have hd := dirtyCost_or s.dirty (batchUpdate cfg.beta cfg.lower s.ref es).2
    linarith
  simp only [acquireStep]
  split_ifs with hend hdirty
  · intro _
    refine ⟨cfg.epoch_pos,?_,?_⟩
    · simp only [Nat.add_mul,Nat.one_mul,Nat.add_zero]
      omega
    · simpa [dirtyCost,hdirty] using hsum
  · intro h
    cases h
  · intro _
    refine ⟨?_,?_,hsum⟩
    · change s.pos+1 < cfg.epochLength
      omega
    · change s.time+1=s.epochs*cfg.epochLength+(s.pos+1)
      omega

theorem epoch_count_bound (cfg : Config) (s : State V) (hp : EpochProgress cfg s) :
    s.epochs ≤ Fintype.card V*cfg.beta^2 := by
  have hu := potential_upper cfg.beta s.ref
  have hn := dirtyCost_nonneg s.dirty
  have hh := hp.2.2
  exact_mod_cast (show (s.epochs:ℤ) ≤ (Fintype.card V:ℤ)*(cfg.beta:ℤ)^2 by linarith)

theorem epoch_time_bound (cfg : Config) (s : State V) (hp : EpochProgress cfg s) :
    s.time < operationBound (V:=V) cfg.beta*cfg.epochLength := by
  have he := epoch_count_bound cfg s hp
  have hm := Nat.mul_le_mul_right cfg.epochLength he
  have ht := hp.2.1
  have hpos := hp.1
  unfold operationBound
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem acquireStep_freeze_bound (cfg : Config) (s : State V) (es : List (Edge V))
    (hp : EpochProgress cfg s) (hf : s.freezeAt=none) (tau : ℕ)
    (ht : (acquireStep cfg s es).freezeAt=some tau) :
    tau ≤ operationBound (V:=V) cfg.beta*cfg.epochLength := by
  have htime := epoch_time_bound cfg s hp
  simp only [acquireStep] at ht
  split_ifs at ht with hend hdirty
  · rw [hf] at ht; cases ht
  · have h := Option.some.inj ht
    omega
  · rw [hf] at ht; cases ht

def AcquisitionInvariant (cfg : Config) (s : State V) : Prop :=
  (s.freezeAt=none → s.aborted=false ∧ EpochProgress cfg s) ∧
  (∀ tau,s.freezeAt=some tau → tau ≤ operationBound (V:=V) cfg.beta*cfg.epochLength)

theorem initial_invariant (cfg : Config) : AcquisitionInvariant cfg (initialState : State V) := by
  constructor
  · intro _
    refine ⟨rfl,cfg.epoch_pos,?_,?_⟩
    · simp [initialState]
    · simp [initialState,dirtyCost,potential_empty]
  · intro tau h
    cases h

theorem step_invariant (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (hs : AcquisitionInvariant cfg s) (a : E) : AcquisitionInvariant cfg (step cfg batch s a) := by
  cases hf : s.freezeAt with
  | none =>
    obtain ⟨ha,hp⟩ := hs.1 hf
    have heq : step cfg batch s a=acquireStep cfg s (batch a) := by simp [step,ha,hf]
    rw [heq]
    constructor
    · intro hn
      refine ⟨?_,acquireStep_progress cfg s _ hp hf hn⟩
      simp only [acquireStep]
      split_ifs <;> exact ha
    · exact acquireStep_freeze_bound cfg s _ hp hf
  | some tau =>
    have ht := freeze_persistent cfg batch s a tau hf
    constructor
    · intro hn
      rw [ht] at hn
      cases hn
    · intro t hh
      rw [ht] at hh
      exact Option.some.inj hh ▸ hs.2 tau hf

theorem runFrom_invariant (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (hs : AcquisitionInvariant cfg s) (as : List E) : AcquisitionInvariant cfg (runFrom cfg batch s as) := by
  induction as generalizing s with
  | nil => exact hs
  | cons a as ih => exact ih _ (step_invariant cfg batch s hs a)

theorem run_invariant (cfg : Config) (batch : E → List (Edge V)) (as : List E) :
    AcquisitionInvariant cfg (run cfg batch as) :=
  runFrom_invariant cfg batch initialState (initial_invariant cfg) as

theorem run_freeze_bound (cfg : Config) (batch : E → List (Edge V)) (as : List E)
    (tau : ℕ) (ht : (run cfg batch as).freezeAt=some tau) :
    tau ≤ operationBound (V:=V) cfg.beta*cfg.epochLength := (run_invariant cfg batch as).2 tau ht

theorem run_frozen_by (cfg : Config) (batch : E → List (Edge V)) (as : List E)
    (hlen : operationBound (V:=V) cfg.beta*cfg.epochLength ≤ as.length) :
    (run cfg batch as).freezeAt ≠ none := by
  intro hf
  have ht := epoch_time_bound cfg _ ((run_invariant cfg batch as).1 hf).2
  rw [run_time] at ht
  omega

end RandomOrderMatching.Acquisition
#print axioms RandomOrderMatching.Acquisition.run_frozen_by
#print axioms RandomOrderMatching.Acquisition.run_freeze_bound
