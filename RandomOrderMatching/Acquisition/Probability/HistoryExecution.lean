import RandomOrderMatching.Acquisition.Probability.HistoryPartition
import RandomOrderMatching.Acquisition.Probability.SuffixEnumeration
import RandomOrderMatching.Streaming.FailureEvents
import RandomOrderMatching.Streaming.BenchmarkPreservation

/-! Exact execution adapters on an observed acquisition history. -/
noncomputable section
open Classical
open scoped BigOperators
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Streaming
open RandomOrderMatching.Probability.Stopping RandomOrderMatching.Probability.Permutation
open RandomOrderMatching.Phases.Execution
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

theorem labelled_prefix_state {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Edge V → List (Edge C)) (label : Fin n→Edge V)
    (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k≤n) :
    run cfg batch ((labelledStream label π).take k)=
      stateAt cfg (fun i => batch (label i)) (permutationStream hn π) k := by
  rw [stateAt,permutation_inputPrefix hn π k hk]
  unfold labelledStream
  rw [←List.map_take,acquisition_run_map]

theorem physicalSuffixValue_labelled {n : ℕ} (hn : 0<n) (w : Edge V→ℕ)
    (cfg : Config) (model : BatchModel (Edge V) C) (label : Fin n→Edge V)
    (π : Equiv.Perm (Fin n)) :
    let t := acquisitionStop hn cfg (fun i => model.copies (label i)) π
    let H := actualReference hn cfg (fun i => model.copies (label i)) π t
    physicalSuffixValue w cfg model (labelledStream label π)=
      ∑ e ∈ outputMatching w (H.image model.parent)
        (fun e => ∃f∈model.copies e,edgeDegree H f<cfg.lower)
        (((List.ofFn π).drop t).map label) (reachedCuts (n-t)),(w e:ℝ) := by
  dsimp only
  unfold physicalSuffixValue
  rw [labelled_final_state hn cfg model.copies label π,labelledStream_length]
  rw [show (stateAt cfg (fun i => model.copies (label i)) (permutationStream hn π) n).freezeAt.getD n=
    acquisitionStop hn cfg (fun i => model.copies (label i)) π from rfl]
  change (∑e∈outputMatching w _ _ _ _,(w e:ℝ))=_
  have hp := labelled_prefix_state hn cfg model.copies label π
    (acquisitionStop hn cfg (fun i => model.copies (label i)) π)
    (acquisitionStop_le hn cfg (fun i => model.copies (label i)) π)
  change run cfg model.copies ((labelledStream label π).take _)=_ at hp
  rw [hp]
  simp only [acquisitionFrozenView,labelledStream,List.map_drop,List.length_map,
    List.length_drop,List.length_ofFn,actualReference]

theorem physicalSuffixValue_on_history {n : ℕ} (hn : 0<n) (w : Edge V→ℕ)
    (cfg : Config) (model : BatchModel (Edge V) C) (label : Fin n→Edge V)
    (σ π : Equiv.Perm (Fin n))
    (hp : π∈stoppedCylinder (acquisitionStop hn cfg (fun i=>model.copies (label i))) σ) :
    let t := acquisitionStop hn cfg (fun i => model.copies (label i)) σ
    let H := actualReference hn cfg (fun i => model.copies (label i)) σ t
    physicalSuffixValue w cfg model (labelledStream label π)=
      ∑ e ∈ outputMatching w (H.image model.parent)
        (fun e => ∃f∈model.copies e,edgeDegree H f<cfg.lower)
        (((List.ofFn π).drop t).map label) (reachedCuts (n-t)),(w e:ℝ) := by
  rw [stoppedCylinder_eq _ (acquisitionStop_causal hn cfg (fun i => model.copies (label i)))] at hp
  have ht := stop_eq_on_cylinder _ (acquisitionStop_causal hn cfg (fun i => model.copies (label i))) σ π hp
  have hH := actualReference_prefix hn cfg (fun i => model.copies (label i)) _
    (acquisitionStop_le hn cfg (fun i => model.copies (label i)) σ) σ π hp
  rw [physicalSuffixValue_labelled hn w cfg model label π]
  dsimp only
  rw [ht,hH]

theorem actual_conditional_event_mean {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n→List (Edge C)) (σ : Equiv.Perm (Fin n))
    (P : Equiv.Perm (Fin n)→Prop) :
    (((stoppedCylinder (acquisitionStop hn cfg batch) σ).filter P).card : ℝ)/
      (stoppedCylinder (acquisitionStop hn cfg batch) σ).card=
    ((Finset.univ.filter (fun ν : Equiv.Perm (remaining
      (positions (acquisitionStop hn cfg batch σ)) σ) =>
      P (extendSuffix (positions (acquisitionStop hn cfg batch σ)) σ ν).val)).card : ℝ)/
      Fintype.card (Equiv.Perm (remaining (positions (acquisitionStop hn cfg batch σ)) σ)) := by
  have hh := acquisition_stopped_suffix_mean hn cfg batch σ
    (fun π => if P π then (1:ℝ) else 0)
  simpa only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one] using hh

theorem actual_global_residual_bound {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n→List (Edge C)) (P : Equiv.Perm (Fin n)→Prop) (p : ℝ)
    (hlocal : ∀σ,
      ((Finset.univ.filter (fun ν : Equiv.Perm (remaining
        (positions (acquisitionStop hn cfg batch σ)) σ) =>
        P (extendSuffix (positions (acquisitionStop hn cfg batch σ)) σ ν).val)).card : ℝ)/
        Fintype.card (Equiv.Perm (remaining (positions (acquisitionStop hn cfg batch σ)) σ))≤p) :
    ((Finset.univ.filter P).card : ℝ)/Fintype.card (Equiv.Perm (Fin n))≤p := by
  apply actual_stopped_event_bound hn cfg batch (Finset.univ.filter P) p
  intro σ
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [actual_conditional_event_mean hn cfg batch σ P]
  exact hlocal σ

end RandomOrderMatching.Acquisition.Probability
