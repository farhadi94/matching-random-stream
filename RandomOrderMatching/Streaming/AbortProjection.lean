import RandomOrderMatching.Streaming.AcquisitionAdapter
import RandomOrderMatching.Acquisition.Invariants
noncomputable section
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph
variable {V C E : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

theorem acquisition_step_aborted (cfg : RandomOrderMatching.Acquisition.Config) (batch : E→List (Edge C))
    (s : RandomOrderMatching.Acquisition.State C) (hs : s.aborted=true) (e : E) :
    (RandomOrderMatching.Acquisition.step cfg batch s e).aborted=true := by
  simp [RandomOrderMatching.Acquisition.step,hs]

theorem acquisition_runFrom_aborted (cfg : RandomOrderMatching.Acquisition.Config) (batch : E→List (Edge C))
    (s : RandomOrderMatching.Acquisition.State C) (hs : s.aborted=true) (l : List E) :
    (RandomOrderMatching.Acquisition.runFrom cfg batch s l).aborted=true := by
  induction l generalizing s with
  | nil => exact hs
  | cons e l ih => exact ih _ (acquisition_step_aborted cfg batch s hs e)

theorem acquisition_prefix_safe (cfg : RandomOrderMatching.Acquisition.Config) (batch : E→List (Edge C))
    (l : List E) (hs : (RandomOrderMatching.Acquisition.run cfg batch l).aborted=false) (i : ℕ) :
    (RandomOrderMatching.Acquisition.run cfg batch (l.take i)).aborted=false := by
  cases hpre : (RandomOrderMatching.Acquisition.run cfg batch (l.take i)).aborted with
  | false => rfl
  | true =>
    have hh := acquisition_runFrom_aborted cfg batch _ hpre (l.drop i)
    have he : RandomOrderMatching.Acquisition.runFrom cfg batch (RandomOrderMatching.Acquisition.run cfg batch (l.take i)) (l.drop i)=
        RandomOrderMatching.Acquisition.run cfg batch l := by
      simp [RandomOrderMatching.Acquisition.run,RandomOrderMatching.Acquisition.runFrom,←List.foldl_append,List.take_append_drop]
    rw [he,hs] at hh
    cases hh

def localAcquisition {A : Type*} : LocalState A V→Option A
  | .acquiring a | .running a _ _ => some a
  | .aborted => none

theorem localAcquisition_step {A : Type*} (w : Edge V→ℕ) (advance : A→Edge V→A)
    (abort : A→Bool) (frozen : A→Option (FrozenView V)) (s : LocalState A V) (e : Edge V) :
    localAcquisition (localStep w advance abort frozen s e)=
      (localAcquisition s).bind (fun a => if abort (advance a e) then none else some (advance a e)) := by
  cases s with
  | aborted => rfl
  | acquiring a =>
    simp only [localStep,localAcquisition,Option.bind_some]
    split_ifs
    · rfl
    · cases hf : frozen (advance a e) <;> rfl
  | running a view suffix =>
    simp only [localStep,localAcquisition,Option.bind_some]
    split_ifs <;> rfl

theorem acquiredLocalRun_projection (w : Edge V→ℕ) (cfg : RandomOrderMatching.Acquisition.Config)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (l : List (Edge V)) :
    localAcquisition (l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit)=
      if (RandomOrderMatching.Acquisition.run cfg model.copies l).aborted then none
      else some (RandomOrderMatching.Acquisition.run cfg model.copies l) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    have hr : RandomOrderMatching.Acquisition.run cfg model.copies (l++[e])=
      RandomOrderMatching.Acquisition.step cfg model.copies (RandomOrderMatching.Acquisition.run cfg model.copies l) e := by
      simp [RandomOrderMatching.Acquisition.run,RandomOrderMatching.Acquisition.runFrom,List.foldl_append]
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change localAcquisition (localStep w (RandomOrderMatching.Acquisition.step cfg model.copies)
      RandomOrderMatching.Acquisition.State.aborted (acquisitionReadView cfg model)
      (l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit) e)=_
    rw [localAcquisition_step,ih,hr]
    cases ha : (RandomOrderMatching.Acquisition.run cfg model.copies l).aborted with
    | false => simp only [Bool.false_eq_true,↓reduceIte,Option.bind_some]
    | true =>
      have hb := acquisition_step_aborted cfg model.copies _ ha e
      simp [ha,hb]

theorem acquiredLocalRun_aborted_answer (w : Edge V→ℕ) (cfg : RandomOrderMatching.Acquisition.Config)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (l : List (Edge V))
    (ha : (RandomOrderMatching.Acquisition.run cfg model.copies l).aborted=true) :
    localAnswer w (l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit)=none := by
  have hp := acquiredLocalRun_projection w cfg model l
  rw [ha] at hp
  simp only [↓reduceIte] at hp
  cases hs : l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit with
  | aborted => rfl
  | acquiring a => simp [hs,localAcquisition] at hp
  | running a view suffix => simp [hs,localAcquisition] at hp

end RandomOrderMatching.Streaming
