import RobustMatching.R8StreamingWrapperRunActual
import RobustMatching.R8StreamingWrapperConfigured
import RobustMatching.R8AcquisitionProvenance
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

theorem boundedIntegerOutput_nonexact_suffix (n Q cap : ℕ) (w : Edge V→ℕ)
    (configs : ℕ→R8Acquisition.Config) (model : R8Acquisition.BatchModel (Edge V) C)
    (l : List (Edge V)) (d : Edge V) (tau : ℕ)
    (hlarge : cap < l.length) (hm : chosenScale l.length∈scales n Q)
    (ht : (R8Acquisition.run (configs (chosenScale l.length)) model.copies l).freezeAt=some tau)
    (hsafe : ∀ i ≤ l.length,
      (R8Acquisition.run (configs (chosenScale l.length)) model.copies (l.take i)).aborted=false) :
    let view := acquisitionFrozenView (configs (chosenScale l.length)) model
      (R8Acquisition.run (configs (chosenScale l.length)) model.copies (l.take tau))
    boundedIntegerOutput n Q cap w configs model l=
      suffixOutput w view.reference (suffixRun w view.reference view.eligible (l.drop tau)) := by
  dsimp only
  unfold boundedIntegerOutput boundedIntegerRun
  rw [outerOutput_overflow_selected n Q cap (fun _ => acquiredLocalInit)
    (fun M => acquiredLocalStep w (configs M) model) (fun _ => localAnswer w) w l hlarge hm]
  rw [acquiredLocalRun_exact w (configs (chosenScale l.length)) model l d tau ht hsafe]
  rfl

/-- The actual unknown-length output is exactly the claimed fixed-host suffix
output on the selected copy's cap-success event. Every operational branch,
scale selection, freeze prefix and suffix buffer has been retained. -/
theorem configured_nonexact_suffix_output (w : Edge V→ℕ) (beta lower LU L0 : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : R8Acquisition.BatchModel (Edge V) C) (l : List (Edge V)) (hnd : l.Nodup)
    (d : Edge V) (tau : ℕ)
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0 < l.length) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q
      (chosenScale l.length) hb hl
    (R8Acquisition.run cfg model.copies l).freezeAt=some tau →
    (∀ i ≤ l.length,(R8Acquisition.run cfg model.copies (l.take i)).aborted=false) →
    configuredBoundedOutput w beta lower LU L0 hb hl model l=
      suffixOutput w (acquisitionFrozenView cfg model (R8Acquisition.run cfg model.copies (l.take tau))).reference
        (suffixRun w (acquisitionFrozenView cfg model (R8Acquisition.run cfg model.copies (l.take tau))).reference
          (acquisitionFrozenView cfg model (R8Acquisition.run cfg model.copies (l.take tau))).eligible (l.drop tau)) := by
  dsimp only
  intro ht hsafe
  exact boundedIntegerOutput_nonexact_suffix _ _ _ w _ model l d tau hlarge
    (configured_selected_active beta lower LU L0 model l hnd hlarge) ht hsafe

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.configured_nonexact_suffix_output
