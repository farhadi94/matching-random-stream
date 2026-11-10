import RandomOrderMatching.Streaming.Configuration
import RandomOrderMatching.Streaming.FreezeTransition
import RandomOrderMatching.Acquisition.Termination
noncomputable section
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

/-- Every nonexact execution's selected concrete acquisition copy freezes,
and the actual stored freeze time lies inside the deterministic rho-prefix.
This uses the insertion/cleanup potential theorem, not a successful-epoch premise. -/
theorem configured_selected_acquisition_freezes (beta lower LU L0 : ℕ)
    (hb : 1≤beta) (hl : lower+1≤beta)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (l : List (Edge V)) (hnd : l.Nodup)
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0<l.length) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q
      (chosenScale l.length) hb hl
    ∃tau,(RandomOrderMatching.Acquisition.run cfg model.copies l).freezeAt=some tau ∧
      100000000*tau≤l.length := by
  dsimp only
  let Q := acquisitionBudget (Fintype.card C) beta
  let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q
    (chosenScale l.length) hb hl
  have hQ : 0<Q := by dsimp [Q,acquisitionBudget]; omega
  have hm : 0<l.length := by
    have hh : 0<fullCapacity (Fintype.card V) Q model.kappa L0 :=
      lt_of_lt_of_le (by positivity : 0<400000000*Q) (le_max_left _ _)
    exact hh.trans hlarge
  have hactive := configured_selected_active beta lower LU L0 model l hnd hlarge
  have hM : 200000000*Q≤chosenScale l.length := (Finset.mem_filter.mp hactive).2
  have he : cfg.epochLength=epochLength Q (chosenScale l.length) :=
    configForScale_epoch hb hl hQ hM
  have hbnd : RandomOrderMatching.Acquisition.operationBound (V:=C) cfg.beta=Q := rfl
  have hprefix := epochLength_prefix_bound (Q:=Q) (chosenScale_bounds hm).1
  have hlen : RandomOrderMatching.Acquisition.operationBound (V:=C) cfg.beta*cfg.epochLength≤l.length := by
    rw [hbnd,he]
    omega
  have hf := RandomOrderMatching.Acquisition.run_frozen_by cfg model.copies l hlen
  cases ht : (RandomOrderMatching.Acquisition.run cfg model.copies l).freezeAt with
  | none => exact (hf ht).elim
  | some tau =>
    refine ⟨tau,rfl,?_⟩
    have hbound := RandomOrderMatching.Acquisition.run_freeze_bound cfg model.copies l tau ht
    rw [hbnd,he] at hbound
    nlinarith

end RandomOrderMatching.Streaming
#print axioms RandomOrderMatching.Streaming.configured_selected_acquisition_freezes
