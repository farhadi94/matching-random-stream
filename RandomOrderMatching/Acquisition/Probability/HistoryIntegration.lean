import RandomOrderMatching.Acquisition.Probability.HistoryExecution

/-! Complete stopped-history averaging with a precise uniform physical-suffix
contract. The local graph/probability theorem is instantiated separately. -/
noncomputable section
open Classical
open scoped BigOperators
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Streaming
open RandomOrderMatching.Probability.Stopping RandomOrderMatching.Probability.Permutation
open RandomOrderMatching.Phases.Execution RandomOrderMatching.Probability.ClockCoupling
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

def historySuffixEvent {n : ℕ} (hn : 0<n) (w : Edge V→ℕ)
    (cfg : Config) (model : BatchModel (Edge V) C) (label : Fin n→Edge V)
    (M : Graph V) (r : ℝ) (σ : Equiv.Perm (Fin n)) :
    Set (Equiv.Perm (Fin (n-acquisitionStop hn cfg (fun i => model.copies (label i)) σ))) :=
  let t := acquisitionStop hn cfg (fun i => model.copies (label i)) σ
  let H := actualReference hn cfg (fun i => model.copies (label i)) σ t
  let e := suffixEnumeration σ t (acquisitionStop_le hn cfg (fun i => model.copies (label i)) σ)
  {ν | (∑ f ∈ outputMatching w (H.image model.parent)
      (fun a => ∃f∈model.copies a,edgeDegree H f<cfg.lower)
      (List.ofFn (fun i => label ((e (ν i)).val))) (reachedCuts (n-t)),(w f:ℝ)) <
    r*(∑ f ∈ actualSurvivingWitness hn cfg (fun i => model.copies (label i)) label M σ,(w f:ℝ))}

/-- All stopping-time conditioning, residual-label reindexing, and physical
execution identifications are discharged. The only modular premise is a
uniform fixed-host guarantee on the displayed actual suffix experiment. -/
theorem physical_suffix_failure_from_fixed_hosts {n : ℕ} (hn : 0<n) (w : Edge V→ℕ)
    (cfg : Config) (model : BatchModel (Edge V) C) (label : Fin n→Edge V)
    (M : Graph V) (r p : ℝ)
    (hlocal : ∀σ,(uniformOrder (n-acquisitionStop hn cfg (fun i => model.copies (label i)) σ)).real
      (historySuffixEvent hn w cfg model label M r σ)≤p) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      physicalSuffixValue w cfg model (labelledStream label π)<
        r*(∑f∈survivingFixedMatching cfg model (labelledStream label π) M,(w f:ℝ)))).card : ℝ)/
      Fintype.card (Equiv.Perm (Fin n))≤p := by
  apply actual_global_residual_bound hn cfg (fun i => model.copies (label i))
  intro σ
  let t := acquisitionStop hn cfg (fun i => model.copies (label i)) σ
  have ht : t≤n := acquisitionStop_le hn cfg (fun i => model.copies (label i)) σ
  rw [residual_event_reindex σ t ht]
  apply le_of_eq_of_le ?_ (hlocal σ)
  congr 1
  ext ν
  let π := (extendSuffix (positions t) σ ((suffixEnumeration σ t ht).permCongr ν)).val
  have hp : π∈stoppedCylinder (acquisitionStop hn cfg (fun i => model.copies (label i))) σ := by
    rw [stoppedCylinder_eq _ (acquisitionStop_causal hn cfg (fun i => model.copies (label i)))]
    exact (extendSuffix (positions t) σ ((suffixEnumeration σ t ht).permCongr ν)).property
  have hv := physicalSuffixValue_on_history hn w cfg model label σ π hp
  have hm := actualSurvivingWitness_eq_on_stopped_history hn cfg
    (fun i => model.copies (label i)) label M σ π hp
  have hl := extended_suffix_reindexed label σ t ht ν
  change (physicalSuffixValue w cfg model (labelledStream label π)<
      r*(∑f∈survivingFixedMatching cfg model (labelledStream label π) M,(w f:ℝ))) ↔ _
  rw [hv,survivingFixedMatching_labelled hn cfg model label M π,hm]
  dsimp only at hv ⊢
  rw [show (((List.ofFn π).drop t).map label)=
    List.ofFn (fun i => label ((suffixEnumeration σ t ht (ν i)).val)) from hl]
  rfl

end RandomOrderMatching.Acquisition.Probability
