import RobustMatching.R8StreamingWrapperLocal
import RobustMatching.R8StreamingWrapperOuter
import RobustMatching.R8AcquisitionState
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

def acquisitionFrozenView (cfg : R8Acquisition.Config)
    (model : R8Acquisition.BatchModel (Edge V) C) (s : R8Acquisition.State C) : FrozenView V where
  reference := s.ref.image model.parent
  eligible e := ∃f∈model.copies e,R8Acquisition.edgeDegree s.ref f<cfg.lower

def acquisitionReadView (cfg : R8Acquisition.Config)
    (model : R8Acquisition.BatchModel (Edge V) C) (s : R8Acquisition.State C) :
    Option (FrozenView V) :=
  match s.freezeAt with
  | none => none
  | some _ => some (acquisitionFrozenView cfg model s)

def acquiredLocalStep (w : Edge V→ℕ) (cfg : R8Acquisition.Config)
    (model : R8Acquisition.BatchModel (Edge V) C) :
    LocalState (R8Acquisition.State C) V→Edge V→LocalState (R8Acquisition.State C) V :=
  localStep w (R8Acquisition.step cfg model.copies) R8Acquisition.State.aborted
    (acquisitionReadView cfg model)

def acquiredLocalInit : LocalState (R8Acquisition.State C) V :=
  .acquiring R8Acquisition.initialState

/-- Complete finite fan-out execution using the actual acquisition state and
original-label phase bank. This definition is independent of the final length.
Its probability/space theorem still needs the acquisition/event contracts. -/
def boundedIntegerRun (n Q cap : ℕ) (w : Edge V→ℕ)
    (configs : ℕ→R8Acquisition.Config) (model : R8Acquisition.BatchModel (Edge V) C)
    (l : List (Edge V)) :=
  outerRun n Q cap (fun _ => acquiredLocalInit)
    (fun M => acquiredLocalStep w (configs M) model) l

def boundedIntegerOutput (n Q cap : ℕ) (w : Edge V→ℕ)
    (configs : ℕ→R8Acquisition.Config) (model : R8Acquisition.BatchModel (Edge V) C)
    (l : List (Edge V)) : Graph V :=
  outerOutput n Q w (fun _ => localAnswer w) (boundedIntegerRun n Q cap w configs model l)

theorem boundedInteger_full_exact (n Q cap : ℕ) (w : Edge V→ℕ)
    (configs : ℕ→R8Acquisition.Config) (model : R8Acquisition.BatchModel (Edge V) C)
    (l : List (Edge V)) (hl : l.length≤cap) :
    boundedIntegerOutput n Q cap w configs model l=
      R7WeightedPhaseAssembly.decode w l.toFinset :=
  outerOutput_full_exact n Q cap _ _ _ w l hl

theorem acquisitionView_reference_subset (cfg : R8Acquisition.Config)
    (model : R8Acquisition.BatchModel (Edge V) C) (s : R8Acquisition.State C)
    (l : List (Edge V)) (hsub : s.ref⊆R8Acquisition.seenCopies model.copies l) :
    (acquisitionFrozenView cfg model s).reference⊆l.toFinset := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  have hs := hsub hf
  simp only [R8Acquisition.seenCopies,List.mem_toFinset,List.mem_flatMap] at hs
  obtain ⟨a,ha,hf⟩ := hs
  have hp := model.parent_mem a f hf
  exact List.mem_toFinset.mpr (hp ▸ ha)

end RobustMatching.R8StreamingWrapper
