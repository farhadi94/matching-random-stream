import RandomOrderMatching.Streaming.OriginalLabels
import RandomOrderMatching.Acquisition.Probability.CapSuccess
import RandomOrderMatching.Streaming.Configuration
noncomputable section
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Acquisition.Probability RandomOrderMatching.Probability.Permutation
variable {V C E : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

/-- The proved uniform-permutation cap bound applies to the actual original
edge list consumed by the wrapper, via a concrete injective label encoding. -/
theorem original_label_cap_failure {m : ℕ} (hm : 0 < m) (cfg : Config)
    (model : BatchModel E C) (label : Fin m→E) (hi : Function.Injective label) (Gamma : ℕ)
    (hfit : operationBound (V:=C) cfg.beta*cfg.epochLength ≤ m)
    (hcap : model.kappa*Gamma ≤ cfg.uCap) :
    ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (run cfg model.copies (labelledStream label pi)).aborted=true)).card : ℝ) /
        Fintype.card (Equiv.Perm (Fin m)) ≤
      operationBound (V:=C) cfg.beta*Real.exp (-(cfg.epochLength:ℝ)*Gamma/m) := by
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hh := actual_cap_failure_probability hm cfg (labelledModel model label hi) Gamma hfit hcap
  have hs (pi : Equiv.Perm (Fin m)) : run cfg model.copies (labelledStream label pi)=
      stateAt cfg (labelledModel model label hi).copies (permutationStream hm pi) m :=
    labelled_final_state hm cfg model.copies label pi
  have he : (Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (run cfg model.copies (labelledStream label pi)).aborted=true)) =
      Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (stateAt cfg (labelledModel model label hi).copies (permutationStream hm pi) m).aborted=true) := by
    apply Finset.filter_congr
    intro pi _
    rw [hs pi]
  rw [he]
  exact hh


/-- Actual selected-copy overflow probability, at the configured floor epoch
length and hard copied-record cap, on the original input permutation space. -/
theorem configured_cap_failure_probability {m : ℕ} (hm : 0 < m)
    (beta lower LU L0 : ℕ) (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : BatchModel (Edge V) C) (label : Fin m→Edge V) (hi : Function.Injective label)
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0 < m) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q (chosenScale m) hb hl
    ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (run cfg model.copies (labelledStream label pi)).aborted=true)).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin m)) ≤ (Q:ℝ)*Real.exp (-(LU:ℝ)) := by
  dsimp only
  let Q := acquisitionBudget (Fintype.card C) beta
  let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q (chosenScale m) hb hl
  have hQ : 0 < Q := by dsimp [Q,acquisitionBudget]; omega
  obtain ⟨hscale,hscale2⟩ := chosenScale_bounds hm
  have hbig : 400000000*Q < m := lt_of_le_of_lt (le_max_left _ _) hlarge
  have hM : 200000000*Q ≤ chosenScale m := by omega
  have he : cfg.epochLength=epochLength Q (chosenScale m) := configForScale_epoch hb hl hQ hM
  have hbnd : operationBound (V:=C) cfg.beta=Q := rfl
  have hp := epochLength_prefix_bound (Q:=Q) hscale
  have hfit : operationBound (V:=C) cfg.beta*cfg.epochLength ≤ m := by rw [hbnd,he]; omega
  have hcap : model.kappa*parentCapacity Q LU ≤ cfg.uCap := le_rfl
  have hh := original_label_cap_failure hm cfg model label hi (parentCapacity Q LU) hfit hcap
  rw [hbnd,he] at hh
  apply hh.trans
  exact mul_le_mul_of_nonneg_left (parentCapacity_exp_bound hQ hM hscale2 hm) (by positivity)

end RandomOrderMatching.Streaming
#print axioms RandomOrderMatching.Streaming.configured_cap_failure_probability
