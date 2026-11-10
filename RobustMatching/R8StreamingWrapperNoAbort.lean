import RobustMatching.R8StreamingWrapperAcquisition
import RobustMatching.R8AcquisitionStateBasic
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut
variable {V C E : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

theorem acquisition_step_aborted (cfg : R8Acquisition.Config) (batch : E→List (Edge C))
    (s : R8Acquisition.State C) (hs : s.aborted=true) (e : E) :
    (R8Acquisition.step cfg batch s e).aborted=true := by
  simp [R8Acquisition.step,hs]

theorem acquisition_runFrom_aborted (cfg : R8Acquisition.Config) (batch : E→List (Edge C))
    (s : R8Acquisition.State C) (hs : s.aborted=true) (l : List E) :
    (R8Acquisition.runFrom cfg batch s l).aborted=true := by
  induction l generalizing s with
  | nil => exact hs
  | cons e l ih => exact ih _ (acquisition_step_aborted cfg batch s hs e)

theorem acquisition_prefix_safe (cfg : R8Acquisition.Config) (batch : E→List (Edge C))
    (l : List E) (hs : (R8Acquisition.run cfg batch l).aborted=false) (i : ℕ) :
    (R8Acquisition.run cfg batch (l.take i)).aborted=false := by
  cases hpre : (R8Acquisition.run cfg batch (l.take i)).aborted with
  | false => rfl
  | true =>
    have hh := acquisition_runFrom_aborted cfg batch _ hpre (l.drop i)
    have he : R8Acquisition.runFrom cfg batch (R8Acquisition.run cfg batch (l.take i)) (l.drop i)=
        R8Acquisition.run cfg batch l := by
      simp [R8Acquisition.run,R8Acquisition.runFrom,←List.foldl_append,List.take_append_drop]
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

theorem acquiredLocalRun_projection (w : Edge V→ℕ) (cfg : R8Acquisition.Config)
    (model : R8Acquisition.BatchModel (Edge V) C) (l : List (Edge V)) :
    localAcquisition (l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit)=
      if (R8Acquisition.run cfg model.copies l).aborted then none
      else some (R8Acquisition.run cfg model.copies l) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    have hr : R8Acquisition.run cfg model.copies (l++[e])=
      R8Acquisition.step cfg model.copies (R8Acquisition.run cfg model.copies l) e := by
      simp [R8Acquisition.run,R8Acquisition.runFrom,List.foldl_append]
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change localAcquisition (localStep w (R8Acquisition.step cfg model.copies)
      R8Acquisition.State.aborted (acquisitionReadView cfg model)
      (l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit) e)=_
    rw [localAcquisition_step,ih,hr]
    cases ha : (R8Acquisition.run cfg model.copies l).aborted with
    | false => simp only [Bool.false_eq_true,↓reduceIte,Option.bind_some]
    | true =>
      have hb := acquisition_step_aborted cfg model.copies _ ha e
      simp [ha,hb]

theorem acquiredLocalRun_aborted_answer (w : Edge V→ℕ) (cfg : R8Acquisition.Config)
    (model : R8Acquisition.BatchModel (Edge V) C) (l : List (Edge V))
    (ha : (R8Acquisition.run cfg model.copies l).aborted=true) :
    localAnswer w (l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit)=none := by
  have hp := acquiredLocalRun_projection w cfg model l
  rw [ha] at hp
  simp only [↓reduceIte] at hp
  cases hs : l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit with
  | aborted => rfl
  | acquiring a => simp [hs,localAcquisition] at hp
  | running a view suffix => simp [hs,localAcquisition] at hp

end RobustMatching.R8StreamingWrapper
