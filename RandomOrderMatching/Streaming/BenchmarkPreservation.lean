import RandomOrderMatching.Streaming.CapFailure
import RandomOrderMatching.Acquisition.Probability.SurvivingBenchmark
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Probability.Permutation RandomOrderMatching.Graph.WeightedMatching
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- The fixed original benchmark with the actual consumed prefix removed. -/
def survivingFixedMatching (cfg : Config) (model : BatchModel (Edge V) C)
    (l : List (Edge V)) (M : Graph V) : Graph V :=
  M \ (l.take ((run cfg model.copies l).freezeAt.getD l.length)).toFinset

theorem labelledStream_toFinset {m : ℕ} (label : Fin m → Edge V)
    (pi : Equiv.Perm (Fin m)) :
    (labelledStream label pi).toFinset=Finset.univ.image label := by
  ext e
  simp only [labelledStream,List.mem_toFinset,List.mem_map,List.mem_ofFn,Finset.mem_image,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,⟨i,rfl⟩,rfl⟩
    exact ⟨pi i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨i,⟨pi.symm i,pi.apply_symm_apply i⟩,rfl⟩

theorem survivingFixedMatching_labelled {m : ℕ} (hm : 0 < m) (cfg : Config)
    (model : BatchModel (Edge V) C) (label : Fin m → Edge V)
    (M : Graph V) (pi : Equiv.Perm (Fin m)) :
    survivingFixedMatching cfg model (labelledStream label pi) M =
      actualSurvivingWitness hm cfg (fun i => model.copies (label i)) label M pi := by
  unfold survivingFixedMatching actualSurvivingWitness acquisitionStop
  rw [labelled_final_state hm cfg model.copies label pi,labelledStream_length]
  unfold labelledStream
  rw [←List.map_take]
  congr 1
  ext e
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]
  simp only [←List.mem_toFinset,ofFn_take_toFinset,Finset.mem_image]

theorem configured_epoch_fraction {m : ℕ} (hm : 0 < m)
    (beta lower LU L0 kappa : ℕ) (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) kappa L0 < m) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := configForScale beta lower (copiedCapacity Q kappa LU) Q (chosenScale m) hb hl
    operationBound (V:=C) cfg.beta*cfg.epochLength ≤ m ∧
      ((operationBound (V:=C) cfg.beta*cfg.epochLength:ℕ):ℝ)/m ≤ 1/100000000 := by
  dsimp only
  let Q := acquisitionBudget (Fintype.card C) beta
  let cfg := configForScale beta lower (copiedCapacity Q kappa LU) Q (chosenScale m) hb hl
  have hQ : 0 < Q := by dsimp [Q,acquisitionBudget]; omega
  obtain ⟨hscale,hscale2⟩ := chosenScale_bounds hm
  have hbig : 400000000*Q < m := lt_of_le_of_lt (le_max_left _ _) hlarge
  have hM : 200000000*Q ≤ chosenScale m := by omega
  have he : cfg.epochLength=epochLength Q (chosenScale m) := configForScale_epoch hb hl hQ hM
  have hbnd : operationBound (V:=C) cfg.beta=Q := rfl
  have hp := epochLength_prefix_bound (Q:=Q) hscale
  rw [hbnd,he]
  constructor
  · omega
  · apply (div_le_iff₀ (Nat.cast_pos.mpr hm)).mpr
    have hh : (100000000:ℝ)*((Q*epochLength Q (chosenScale m):ℕ):ℝ) ≤ m := by
      exact_mod_cast hp
    linarith

/-- The selected unknown-length acquisition preserves a fixed original
matching, expressed directly through the consumed original-edge list. -/
theorem configured_witness_failure_probability {m : ℕ} (hm : 0 < m)
    (beta lower LU L0 : ℕ) (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : BatchModel (Edge V) C) (label : Fin m → Edge V) (hi : Function.Injective label)
    (w : Edge V → ℕ) (W : ℕ) (hW : 0 < W) (M : Graph V)
    (hMG : M ⊆ Finset.univ.image label) (hw : ∀ e ∈ M,w e ≤ W)
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0 < m) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q (chosenScale m) hb hl
    ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ survivingFixedMatching cfg model (labelledStream label pi) M,(w e:ℝ)) <
        (1-2*(1/100000000:ℝ))*(∑ e ∈ M,(w e:ℝ)))).card:ℝ)/
      Fintype.card (Equiv.Perm (Fin m)) ≤
      Real.exp (-(1/100000000:ℝ)*(∑ e ∈ M,(w e:ℝ))/(3*W)) := by
  dsimp only
  let Q := acquisitionBudget (Fintype.card C) beta
  let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q (chosenScale m) hb hl
  have hf := configured_epoch_fraction (V:=V) (C:=C) hm beta lower LU L0 model.kappa hb hl hlarge
  have hh := actual_fixed_witness_preserved hm cfg (fun i => model.copies (label i))
    label hi M hMG w W (1/100000000) (Nat.cast_pos.mpr hW) (by norm_num)
    (fun e he => by exact_mod_cast hw e he) hf.1 hf.2
  change _ ≤ Real.exp _
  have he : (Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ survivingFixedMatching cfg model (labelledStream label pi) M,(w e:ℝ)) <
        (1-2*(1/100000000:ℝ))*(∑ e ∈ M,(w e:ℝ)))) =
      Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ actualSurvivingWitness hm cfg (fun i => model.copies (label i)) label M pi,(w e:ℝ)) <
        (1-2*(1/100000000:ℝ))*(∑ e ∈ M,(w e:ℝ))) := by
    apply Finset.filter_congr
    intro pi _
    rw [survivingFixedMatching_labelled hm cfg model label M pi]
  rw [show _ = _ from he]
  exact hh

/-- On the nonexact full-buffer branch, the fixed-optimum loss probability is
at most exp(-L0). The exponent uses the actual original graph size bound. -/
theorem configured_optimum_witness_failure {m : ℕ} (hm : 0 < m)
    (beta lower LU L0 : ℕ) (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : BatchModel (Edge V) C) (label : Fin m → Edge V) (hi : Function.Injective label)
    (w : Edge V → ℕ) (hk : 0 < model.kappa)
    (hw : ∀ e ∈ Finset.univ.image label,1 ≤ w e ∧ w e ≤ model.kappa)
    (M : Graph V) (hMG : M ⊆ Finset.univ.image label)
    (hopt : (∑ e ∈ M,(w e:ℝ))=opt (fun e => (w e:ℝ)) (Finset.univ.image label))
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0 < m) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q (chosenScale m) hb hl
    ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ survivingFixedMatching cfg model (labelledStream label pi) M,(w e:ℝ)) <
        (1-2*(1/100000000:ℝ))*opt (fun e => (w e:ℝ)) (Finset.univ.image label))).card:ℝ)/
      Fintype.card (Equiv.Perm (Fin m)) ≤ Real.exp (-(L0:ℝ)) := by
  have hh := configured_witness_failure_probability hm beta lower LU L0 hb hl model label hi
    w model.kappa hk M hMG (fun e he => (hw e (hMG he)).2) hlarge
  rw [hopt] at hh
  apply hh.trans
  let l := labelledStream label (Equiv.refl _)
  have hnd : l.Nodup := labelledStream_nodup label hi _
  have he : l.toFinset=Finset.univ.image label := labelledStream_toFinset label _
  have hlen : l.length=m := labelledStream_length label _
  have hn : 0 < Fintype.card V := by
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [(label ⟨0,hm⟩).property]; decide)
    exact Fintype.card_pos_iff.mpr ⟨v⟩
  have hx := nonexact_prefix_exponent l hnd w (fun e he' => (hw e (he ▸ he')).1)
    hn (acquisitionBudget (Fintype.card C) beta) model.kappa L0 hk (by simpa only [hlen] using hlarge)
  rw [he,←RandomOrderMatching.Phases.WeightedState.opt_eq_natOpt] at hx
  exact hx

end RandomOrderMatching.Streaming
#print axioms RandomOrderMatching.Streaming.configured_optimum_witness_failure
