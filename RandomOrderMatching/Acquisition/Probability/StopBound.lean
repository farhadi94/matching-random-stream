import RandomOrderMatching.Acquisition.Probability.ResidualHost
import RandomOrderMatching.Acquisition.Termination

/-! Original-optimum preservation instantiated at the actual potential-bounded
freeze. The enclosing-prefix bound is derived from the executed acquisition. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Graph.WeightedMatching
variable {V O : Type*} [Fintype V] [DecidableEq V] [DecidableEq O]

theorem acquisitionStop_progress {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (π : Equiv.Perm (Fin n)) :
    acquisitionStop hn cfg batch π ≤ operationBound (V:=V) cfg.beta*cfg.epochLength := by
  let as := inputPrefix (permutationStream hn π) n
  have hlen : as.length=n := by simp [as,inputPrefix]
  cases hs : (run cfg batch as).freezeAt with
  | none =>
      have hh := epoch_time_bound cfg _ ((run_invariant cfg batch as).1 hs).2
      rw [run_time,hlen] at hh
      have ht : acquisitionStop hn cfg batch π=n := by
        change (run cfg batch as).freezeAt.getD n=n
        rw [hs]
        rfl
      omega
  | some t =>
      have hh := run_freeze_bound cfg batch as t hs
      have ht : acquisitionStop hn cfg batch π=t := by
        change (run cfg batch as).freezeAt.getD n=t
        rw [hs]
        rfl
      omega

theorem actual_host_preserved {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (label : Fin n → Edge O) (hi : Function.Injective label)
    (w : Edge O → ℕ) (W ρ : ℝ) (hW : 0<W) (hρ : 0≤ρ)
    (hw : ∀ e ∈ Finset.univ.image label,(w e : ℝ)≤W)
    (hfit : operationBound (V:=V) cfg.beta*cfg.epochLength≤n)
    (hfrac : ((operationBound (V:=V) cfg.beta*cfg.epochLength : ℕ) : ℝ)/n≤ρ) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      opt (fun e => (w e : ℝ)) (originalHost hn cfg model label π) <
        (1-2*ρ)*opt (fun e => (w e : ℝ)) (Finset.univ.image label))).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin n)) ≤
        Real.exp (-ρ*opt (fun e => (w e : ℝ)) (Finset.univ.image label)/(3*W)) :=
  actual_host_prefix_preservation hn cfg model label hi w
    (operationBound (V:=V) cfg.beta*cfg.epochLength) hfit W ρ hW hρ hw hfrac
    (acquisitionStop_progress hn cfg model.copies)

end RandomOrderMatching.Acquisition.Probability
