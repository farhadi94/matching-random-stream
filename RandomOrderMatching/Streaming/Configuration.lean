import RandomOrderMatching.Streaming.AcquisitionAdapter
import RandomOrderMatching.Streaming.CapParameters
noncomputable section
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option linter.unusedSectionVars false

def acquisitionBudget (N beta : ℕ) : ℕ := N*beta^2+1

def configForScale (beta lower uCap Q M : ℕ) (hb : 1≤beta) (hl : lower+1≤beta) :
    RandomOrderMatching.Acquisition.Config where
  beta := beta
  lower := lower
  epochLength := max 1 (epochLength Q M)
  uCap := uCap
  beta_pos := hb
  lower_gap := hl
  epoch_pos := lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _)

theorem configForScale_epoch {beta lower uCap Q M : ℕ} (hb : 1≤beta)
    (hl : lower+1≤beta) (hQ : 0<Q) (hM : 200000000*Q≤M) :
    (configForScale beta lower uCap Q M hb hl).epochLength=epochLength Q M := by
  apply max_eq_right
  exact epochLength_pos hQ hM

/-- Fixed-parameter bounded-integer wrapper, for a supplied concrete original
batch model. All scales are chosen before seeing the stream; only EOF chooses
which copy's answer is returned. -/
def configuredBoundedOutput (w : Edge V→ℕ) (beta lower LU L0 : ℕ)
    (hb : 1≤beta) (hl : lower+1≤beta)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (l : List (Edge V)) : Graph V :=
  let Q := acquisitionBudget (Fintype.card C) beta
  let cap := fullCapacity (Fintype.card V) Q model.kappa L0
  let uCap := copiedCapacity Q model.kappa LU
  boundedIntegerOutput (Fintype.card V) Q cap w
    (fun M => configForScale beta lower uCap Q M hb hl) model l

theorem configured_full_exact (w : Edge V→ℕ) (beta lower LU L0 : ℕ)
    (hb : 1≤beta) (hl : lower+1≤beta)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (l : List (Edge V))
    (hsmall : l.length≤fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0) :
    configuredBoundedOutput w beta lower LU L0 hb hl model l=
      RandomOrderMatching.Phases.Execution.decode w l.toFinset := by
  exact boundedInteger_full_exact _ _ _ _ _ _ _ hsmall

theorem configured_selected_active (beta lower LU L0 : ℕ)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (l : List (Edge V)) (hnd : l.Nodup)
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0<l.length) :
    chosenScale l.length∈scales (Fintype.card V) (acquisitionBudget (Fintype.card C) beta) :=
  selected_copy_active_on_nonexact l hnd _ _ _ (by unfold acquisitionBudget; omega) hlarge

end RandomOrderMatching.Streaming
