import RandomOrderMatching.Acquisition.Termination

noncomputable section
open Classical
namespace RandomOrderMatching.Acquisition
open RandomOrderMatching.Graph
variable {V E : Type*} [Fintype V] [DecidableEq V]

theorem batchUpdate_append (beta lower : ℕ) (H : Graph V) (as bs : List (Edge V)) :
    batchUpdate beta lower H (as++bs)=
      ((batchUpdate beta lower (batchUpdate beta lower H as).1 bs).1,
       (batchUpdate beta lower H as).2 || (batchUpdate beta lower (batchUpdate beta lower H as).1 bs).2) := by
  induction as generalizing H with
  | nil => simp [batchUpdate]
  | cons a as ih => simp [batchUpdate,ih,Bool.or_assoc]

/-- Exact concrete execution strictly inside a single acquisition epoch. -/
theorem runFrom_interior (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (as : List E) (hf : s.freezeAt=none) (ha : s.aborted=false)
    (hlen : s.pos+as.length < cfg.epochLength) :
    runFrom cfg batch s as=
      {s with ref:=(batchUpdate cfg.beta cfg.lower s.ref (as.flatMap batch)).1,
              time:=s.time+as.length,pos:=s.pos+as.length,
              dirty:=s.dirty || (batchUpdate cfg.beta cfg.lower s.ref (as.flatMap batch)).2} := by
  induction as generalizing s with
  | nil => simp [runFrom,batchUpdate]
  | cons a as ih =>
    have hne : s.pos+1 ≠ cfg.epochLength := by simp only [List.length_cons] at hlen; omega
    let s' : State V := {s with ref:=(batchUpdate cfg.beta cfg.lower s.ref (batch a)).1, time:=s.time+1,pos:=s.pos+1,dirty:=s.dirty || (batchUpdate cfg.beta cfg.lower s.ref (batch a)).2}
    have hs : step cfg batch s a=s' := by simp [step,hf,ha,acquireStep,hne,s']
    have hh := ih s' hf ha (show s'.pos+as.length<cfg.epochLength by
      dsimp [s']; simp only [List.length_cons] at hlen; omega)
    change runFrom cfg batch (step cfg batch s a) as=_
    rw [hs,hh]
    simp [s',List.flatMap_cons,batchUpdate_append,Bool.or_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- A whole epoch, including its actual first-empty-epoch freeze transition. -/
theorem runFrom_epoch (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (as : List E) (hf : s.freezeAt=none) (ha : s.aborted=false)
    (hp : s.pos=0) (hlen : as.length=cfg.epochLength) :
    runFrom cfg batch s as=
      if s.dirty || (batchUpdate cfg.beta cfg.lower s.ref (as.flatMap batch)).2 then
        {s with ref:=(batchUpdate cfg.beta cfg.lower s.ref (as.flatMap batch)).1,
                time:=s.time+cfg.epochLength,pos:=0,epochs:=s.epochs+1,dirty:=false}
      else
        {s with ref:=(batchUpdate cfg.beta cfg.lower s.ref (as.flatMap batch)).1,
                time:=s.time+cfg.epochLength,pos:=0,dirty:=false,freezeAt:=some (s.time+cfg.epochLength)} := by
  have hne : as≠[] := by intro h; simp [h] at hlen; have := cfg.epoch_pos; omega
  let bs := as.dropLast
  let a := as.getLast hne
  have heq : bs++[a]=as := List.dropLast_append_getLast hne
  have hblen : bs.length+1=cfg.epochLength := by
    have hh := congrArg List.length heq
    simpa [hlen] using hh
  have hinter := runFrom_interior cfg batch s bs hf ha (by rw [hp]; omega)
  rw [←heq,runFrom_append,hinter]
  change step cfg batch _ a=_
  simp only [step,hf,ha,Bool.false_eq_true,ite_false,ite_true,acquireStep]
  simp only [hp,Nat.zero_add,hblen,ite_true,List.flatMap_append,List.flatMap_singleton,
    batchUpdate_append,Prod.fst,Prod.snd]
  simp only [Bool.or_assoc]
  have htime : s.time+bs.length+1=s.time+cfg.epochLength := by omega
  simp only [htime]

/-- Every copied label in an actual frozen epoch was non-insertable in its unchanged initial reference. -/
theorem empty_epoch_observation (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (as : List E) (hf : s.freezeAt=none) (ha : s.aborted=false)
    (hp : s.pos=0) (hlen : as.length=cfg.epochLength)
    (hfreeze : (runFrom cfg batch s as).freezeAt≠none) :
    (runFrom cfg batch s as).ref=s.ref ∧
    ∀ a∈as,∀ e∈batch a,¬insertable cfg.lower s.ref e := by
  have hh := runFrom_epoch cfg batch s as hf ha hp hlen
  have hflag : (batchUpdate cfg.beta cfg.lower s.ref (as.flatMap batch)).2=false := by
    rw [hh] at hfreeze
    split_ifs at hfreeze with hd
    · exact (hfreeze hf).elim
    · have := Bool.eq_false_iff.mpr hd
      exact (Bool.or_eq_false_iff.mp this).2
  have hno := batchUpdate_noinsert cfg.beta cfg.lower s.ref (as.flatMap batch) hflag
  have hall := (batchUpdate_false_iff cfg.beta cfg.lower s.ref (as.flatMap batch)).mp hflag
  constructor
  · rw [hh]
    split_ifs <;> exact hno
  · intro a ha e he
    exact hall e (List.mem_flatMap.mpr ⟨a,ha,he⟩)

end RandomOrderMatching.Acquisition
#print axioms RandomOrderMatching.Acquisition.empty_epoch_observation
