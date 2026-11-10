import RobustMatching.R8StreamingWrapperAcquisition
import RobustMatching.R8StreamingWrapperFreeze
import RobustMatching.R8StreamingWrapperPrefix
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

/-- On the concrete acquisition cap-success path, the wrapper's terminal
state is precisely the actual acquisition state together with the suffix
algorithm initialized at its actual stored first-freeze prefix. -/
theorem acquiredLocalRun_exact (w : Edge V → ℕ) (cfg : R8Acquisition.Config)
    (model : R8Acquisition.BatchModel (Edge V) C) (l : List (Edge V)) (d : Edge V)
    (tau : ℕ) (ht : (R8Acquisition.run cfg model.copies l).freezeAt=some tau)
    (hsafe : ∀ i ≤ l.length,(R8Acquisition.run cfg model.copies (l.take i)).aborted=false) :
    l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit=
      .running (R8Acquisition.run cfg model.copies l)
        (acquisitionFrozenView cfg model (R8Acquisition.run cfg model.copies (l.take tau)))
        (suffixRun w
          (acquisitionFrozenView cfg model (R8Acquisition.run cfg model.copies (l.take tau))).reference
          (acquisitionFrozenView cfg model (R8Acquisition.run cfg model.copies (l.take tau))).eligible
          (l.drop tau)) := by
  let advance := R8Acquisition.step cfg model.copies
  let read := acquisitionReadView cfg model
  let a0 : R8Acquisition.State C := R8Acquisition.initialState
  let a := R8Acquisition.run cfg model.copies (l.take tau)
  let view := acquisitionFrozenView cfg model a
  obtain ⟨htpos,htlen⟩ := list_freeze_valid cfg model.copies l d tau ht
  have hi : tau-1 < l.length := by omega
  let pre := l.take (tau-1)
  let e := l[tau-1]
  have hprelen : pre.length=tau-1 := by simp [pre,Nat.min_eq_left (by omega : tau-1 ≤ l.length)]
  have htakes (i : ℕ) (hip : i ≤ pre.length) : pre.take i=l.take i := by
    have hij : i ≤ tau-1 := by omega
    simp [pre,List.take_take,Nat.min_eq_left hij]
  have hsp : ∀ i ≤ pre.length,R8Acquisition.State.aborted ((pre.take i).foldl advance a0)=false := by
    intro i hip
    rw [htakes i hip]
    exact hsafe i (by omega)
  have hvp : ∀ i ≤ pre.length,read ((pre.take i).foldl advance a0)=none := by
    intro i hip
    rw [htakes i hip]
    have hh := list_before_freeze_none cfg model.copies l d tau i (by omega) ht
    change acquisitionReadView cfg model (R8Acquisition.run cfg model.copies (l.take i))=none
    simp [acquisitionReadView,hh]
  have htake : l.take tau=pre++[e] := by
    have he : tau=(tau-1)+1 := by omega
    rw [he,List.take_succ_eq_append_getElem hi]
  have hstep : advance (pre.foldl advance a0) e=a := by
    dsimp only [a]
    rw [htake]
    simp [R8Acquisition.run,R8Acquisition.runFrom,List.foldl_append,advance,a0]
  have hsa : R8Acquisition.State.aborted a=false := hsafe tau htlen
  have hva : read a=some view := by
    have hh := list_freeze_restrict cfg model.copies l d tau tau htlen le_rfl ht
    dsimp [read,a,view]
    simp only [acquisitionReadView,hh]
  have hfreeze : localRun w advance R8Acquisition.State.aborted read (.acquiring a0) (l.take tau)=
      .running a view (suffixInit view.reference) := by
    rw [htake]
    have hh := localRun_first_freeze_step w advance R8Acquisition.State.aborted read
      (.acquiring a0) pre e (pre.foldl advance a0) view
      (localRun_before_freeze w advance R8Acquisition.State.aborted read a0 pre hsp hvp)
      (by simpa only [hstep] using hsa) (by simpa only [hstep] using hva)
    simpa only [hstep] using hh
  have htail : ∀ i ≤ (l.drop tau).length,
      R8Acquisition.State.aborted (((l.drop tau).take i).foldl advance a)=false := by
    intro i hip
    change (R8Acquisition.runFrom cfg model.copies
      (R8Acquisition.run cfg model.copies (l.take tau)) ((l.drop tau).take i)).aborted=false
    rw [run_take_append]
    exact hsafe (tau+i) (by simp only [List.length_drop] at hip; omega)
  have hh := localRun_after_freeze w advance R8Acquisition.State.aborted read (.acquiring a0)
    (l.take tau) (l.drop tau) a view hfreeze htail
  rw [List.take_append_drop] at hh
  have hlast : (l.drop tau).foldl advance a=R8Acquisition.run cfg model.copies l := by
    dsimp [a,advance,R8Acquisition.run,R8Acquisition.runFrom]
    rw [←List.foldl_append,List.take_append_drop]
  rw [hlast] at hh
  exact hh

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.acquiredLocalRun_exact
