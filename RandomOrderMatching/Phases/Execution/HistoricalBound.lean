import RandomOrderMatching.Phases.Execution.Output
import RandomOrderMatching.HistoricalDeletion.Matching
import RandomOrderMatching.Graph.MarkedPair.CutWitnesses

/-! Unconditional historical matching certificates for the concrete
original-label bank and its actual returned matching. No submodularity,
closure-time schedule, host evolution, or decoder bound is assumed. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Phases.Execution
open RandomOrderMatching.Graph RandomOrderMatching.Phases.WeightedState
open RandomOrderMatching.Graph.WeightedMatching RandomOrderMatching.Graph.MarkedPair
open RandomOrderMatching.Graph.BipartiteExchange RandomOrderMatching.Graph.MarkedPair.CutWitnesses
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem concrete_phase_matching_budget
    (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (c : ℕ) (P T : Graph V)
    (hP : ∀ e ∈ P, e ∈ initial H eligible stream c ∨ e ∈ stream.drop c)
    (hTP : T ⊆ P) (hT : Matching T) :
    (∑ e ∈ T, (w e : ℝ)) +
      pathValue (fun e => (w e : ℝ)) (initial H eligible stream c) (covered T) ≤
        2 * opt (fun e => (w e : ℝ)) (phaseFinal w H eligible stream c) := by
  have hh := RandomOrderMatching.HistoricalDeletion.Matching.historical_every_matching
    (fun e => (w e : ℝ)) (fun _ => by positivity)
    (phaseHost w H eligible stream c)
    (fun i j hij => phaseHost_mono w H eligible stream c hij)
    (stream.drop c).length P
    (fun e he => phase_historical_closure w H eligible stream c e (hP e he)) T hTP hT
  rwa [phaseHost_zero,phaseHost_terminal] at hh

/-- All selected repair-parent types are covered: shared H/U originals or
labels past any bracket endpoint later than the actual phase cutoff. -/
theorem bank_historical_matching_budget
    (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (c t : ℕ)
    (hc : c ∈ activeCuts cuts stream) (hct : c ≤ t) (P T : Graph V)
    (hP : ∀ e ∈ P, e ∈ sharedBase H eligible stream ∨ e ∈ stream.drop t)
    (hTP : T ⊆ P) (hT : Matching T) :
    (∑ e ∈ T, (w e : ℝ)) +
      pathValue (fun e => (w e : ℝ)) (initial H eligible stream c) (covered T) ≤
        2 * (∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ)) := by
  have hh := concrete_phase_matching_budget w H eligible stream c P T
    (fun e he => repair_parent_initial_or_tested H eligible stream hct e (hP e he)) hTP hT
  have ho := phase_value_le_output w H eligible stream cuts c hc
  linarith

/-- Concrete bank to actual original cut-deletion optima. The analytic
support is genuinely present because its cutoff precedes the phase cutoff. -/
theorem bank_original_cut_transfer
    (w : Edge V → ℕ) (H A : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (a c t : ℕ)
    (hc : c ∈ activeCuts cuts stream) (hac : a ≤ c) (hct : c ≤ t)
    (hA : A ⊆ initial H eligible stream a) (cut : Finset V) (hcross : Crosses A cut)
    (P T : Graph V)
    (hP : ∀ e ∈ P, e ∈ sharedBase H eligible stream ∨ e ∈ stream.drop t)
    (hTP : T ⊆ P) (hT : Matching T) :
    opt (fun e => (w e : ℝ)) (deleteVertices A (covered T ∩ cut)) +
    opt (fun e => (w e : ℝ)) (deleteVertices A (covered T \ cut)) +
    (∑ e ∈ T, (w e : ℝ)) ≤
      2 * (∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ)) := by
  have ha : A ⊆ initial H eligible stream c := hA.trans (early_base_subset_initial H eligible stream hac)
  have hR : covered T \ cut ⊆ Finset.univ \ cut := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hv).2⟩
  have hh := deletion_optima_le_pathValue (fun e => (w e : ℝ)) ha hcross
    (Finset.inter_subset_right : covered T ∩ cut ⊆ cut) hR
  have heq : (covered T ∩ cut) ∪ (covered T \ cut) = covered T := by
    ext v
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  rw [heq] at hh
  have hb := bank_historical_matching_budget w H eligible stream cuts c t hc hct P T hP hTP hT
  linarith

end RandomOrderMatching.Phases.Execution
#print axioms RandomOrderMatching.Phases.Execution.bank_original_cut_transfer
