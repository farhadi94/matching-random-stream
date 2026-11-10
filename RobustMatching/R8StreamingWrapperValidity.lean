import RobustMatching.R8StreamingWrapperTerminal
import RobustMatching.R8StreamingWrapperNoAbort
import RobustMatching.R8StreamingWrapperFreezeActual
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R7WeightedPhaseAssembly
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

theorem boundedIntegerOutput_valid_of_freeze (n Q cap : ℕ) (w : Edge V→ℕ)
    (configs : ℕ→R8Acquisition.Config) (model : R8Acquisition.BatchModel (Edge V) C)
    (l : List (Edge V)) (d : Edge V) (hlarge : cap < l.length)
    (hm : chosenScale l.length∈scales n Q)
    (hf : (R8Acquisition.run (configs (chosenScale l.length)) model.copies l).freezeAt≠none) :
    Matching (boundedIntegerOutput n Q cap w configs model l) ∧
      boundedIntegerOutput n Q cap w configs model l⊆l.toFinset := by
  let cfg := configs (chosenScale l.length)
  cases ha : (R8Acquisition.run cfg model.copies l).aborted with
  | true =>
    have he : boundedIntegerOutput n Q cap w configs model l=fallbackRun l := by
      unfold boundedIntegerOutput boundedIntegerRun
      rw [outerOutput_overflow_selected n Q cap (fun _ => acquiredLocalInit)
        (fun M => acquiredLocalStep w (configs M) model) (fun _ => localAnswer w) w l hlarge hm]
      rw [acquiredLocalRun_aborted_answer w cfg model l ha]
      rfl
    rw [he]
    exact ⟨fallbackRun_matching l,fallbackRun_subset l⟩
  | false =>
    have hsafe : ∀ i ≤ l.length,(R8Acquisition.run cfg model.copies (l.take i)).aborted=false :=
      fun i _ => acquisition_prefix_safe cfg model.copies l ha i
    cases ht : (R8Acquisition.run cfg model.copies l).freezeAt with
    | none => exact (hf ht).elim
    | some tau =>
      let view := acquisitionFrozenView cfg model (R8Acquisition.run cfg model.copies (l.take tau))
      have he := boundedIntegerOutput_nonexact_suffix n Q cap w configs model l d tau hlarge hm ht hsafe
      change boundedIntegerOutput n Q cap w configs model l=
        suffixOutput w view.reference (suffixRun w view.reference view.eligible (l.drop tau)) at he
      rw [he]
      have hs := suffixOutput_spec w view.reference view.eligible (l.drop tau)
      refine ⟨hs.1,hs.2.trans ?_⟩
      have hH : view.reference⊆(l.take tau).toFinset :=
        acquisitionView_reference_subset cfg model _ _ (R8Acquisition.run_ref_subset cfg model.copies _)
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact List.mem_toFinset.mpr (List.take_subset _ _ (List.mem_toFinset.mp (hH he)))
      · exact List.mem_toFinset.mpr (List.drop_subset _ _ (List.mem_toFinset.mp he))

/-- Every execution returns a matching of the input, including all overflow
and approximation-failure executions. No probabilistic event is a premise. -/
theorem configured_output_valid (w : Edge V→ℕ) (beta lower LU L0 : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : R8Acquisition.BatchModel (Edge V) C) (l : List (Edge V)) (hnd : l.Nodup) :
    Matching (configuredBoundedOutput w beta lower LU L0 hb hl model l) ∧
      configuredBoundedOutput w beta lower LU L0 hb hl model l⊆l.toFinset := by
  let Q := acquisitionBudget (Fintype.card C) beta
  let cap := fullCapacity (Fintype.card V) Q model.kappa L0
  by_cases hsmall : l.length ≤ cap
  · rw [configured_full_exact w beta lower LU L0 hb hl model l hsmall]
    exact ⟨decode_matching _ _,decode_subset _ _⟩
  · have hlarge : cap < l.length := by omega
    have hp : 0 < l.length := by omega
    let d := l[0]
    obtain ⟨tau,ht,_⟩ := configured_selected_acquisition_freezes beta lower LU L0 hb hl model l hnd hlarge
    exact boundedIntegerOutput_valid_of_freeze _ _ _ w _ model l d hlarge
      (configured_selected_active beta lower LU L0 model l hnd hlarge)
      (by rw [ht]; simp)

theorem boundedIntegerOutput_no_selected (n Q cap : ℕ) (w : Edge V→ℕ)
    (configs : ℕ→R8Acquisition.Config) (model : R8Acquisition.BatchModel (Edge V) C)
    (l : List (Edge V)) (hlarge : cap < l.length)
    (hm : chosenScale l.length∉scales n Q) :
    boundedIntegerOutput n Q cap w configs model l=fallbackRun l := by
  unfold boundedIntegerOutput boundedIntegerRun outerOutput
  rw [(outerRun_fields n Q cap (fun _ => acquiredLocalInit)
    (fun M => acquiredLocalStep w (configs M) model) l).2.1,bufferRun_exact,if_neg (by omega)]
  have hs : selectedAnswer n Q (fun _ => localAnswer w)
      (outerRun n Q cap (fun _ => acquiredLocalInit)
        (fun M => acquiredLocalStep w (configs M) model) l)=none := by
    simp [selectedAnswer,(outerRun_fields n Q cap (fun _ => acquiredLocalInit)
      (fun M => acquiredLocalStep w (configs M) model) l).1,hm]
  rw [hs]
  exact (outerRun_fields n Q cap (fun _ => acquiredLocalInit)
    (fun M => acquiredLocalStep w (configs M) model) l).2.2.1

/-- Validity holds even for repeated input edges. If repetitions push the
EOF scale outside the preallocated range, the fallback branch is selected. -/
theorem configured_output_valid_all (w : Edge V→ℕ) (beta lower LU L0 : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : R8Acquisition.BatchModel (Edge V) C) (l : List (Edge V)) :
    Matching (configuredBoundedOutput w beta lower LU L0 hb hl model l) ∧
      configuredBoundedOutput w beta lower LU L0 hb hl model l⊆l.toFinset := by
  let Q := acquisitionBudget (Fintype.card C) beta
  let cap := fullCapacity (Fintype.card V) Q model.kappa L0
  let configs := fun M => configForScale beta lower (copiedCapacity Q model.kappa LU) Q M hb hl
  have hQ : 0 < Q := by dsimp [Q,acquisitionBudget]; omega
  by_cases hsmall : l.length ≤ cap
  · rw [configured_full_exact w beta lower LU L0 hb hl model l hsmall]
    exact ⟨decode_matching _ _,decode_subset _ _⟩
  · have hlarge : cap < l.length := by omega
    have hp : 0 < l.length := by omega
    let d := l[0]
    by_cases hm : chosenScale l.length∈scales (Fintype.card V) Q
    · have hM : 200000000*Q ≤ chosenScale l.length := (Finset.mem_filter.mp hm).2
      have he : (configs (chosenScale l.length)).epochLength=epochLength Q (chosenScale l.length) :=
        configForScale_epoch hb hl hQ hM
      have hbnd : R8Acquisition.operationBound (V:=C) (configs (chosenScale l.length)).beta=Q := rfl
      have hprefix := epochLength_prefix_bound (Q:=Q) (chosenScale_bounds hp).1
      have hfit : R8Acquisition.operationBound (V:=C) (configs (chosenScale l.length)).beta*
          (configs (chosenScale l.length)).epochLength ≤ l.length := by rw [hbnd,he]; omega
      exact boundedIntegerOutput_valid_of_freeze _ _ _ w configs model l d hlarge hm
        (R8Acquisition.run_frozen_by _ model.copies l hfit)
    · have hh := boundedIntegerOutput_no_selected (Fintype.card V) Q cap w configs model l hlarge hm
      change boundedIntegerOutput (Fintype.card V) Q cap w configs model l=_ at hh
      change Matching (boundedIntegerOutput (Fintype.card V) Q cap w configs model l) ∧
        boundedIntegerOutput (Fintype.card V) Q cap w configs model l⊆l.toFinset
      rw [hh]
      exact ⟨fallbackRun_matching l,fallbackRun_subset l⟩

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.configured_output_valid

#print axioms RobustMatching.R8StreamingWrapper.configured_output_valid_all
