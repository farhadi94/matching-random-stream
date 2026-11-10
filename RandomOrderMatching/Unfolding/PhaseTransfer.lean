import RandomOrderMatching.Unfolding.PhaseLifting
import RandomOrderMatching.Algebra.Tutte.RealWeights

/-! Unconditional historical and profile wrappers, instantiating the fully
proved actual-graph Tutte interpretation. No submodularity or determinant
exchange hypothesis remains in these theorem statements. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false

namespace RandomOrderMatching.Unfolding.PhaseLifting
open RandomOrderMatching.Graph RandomOrderMatching.Graph.MarkedPair
open RandomOrderMatching.Graph.WeightedMatching RandomOrderMatching.Graph.BipartiteExchange
open RandomOrderMatching.HistoricalDeletion.Potential RandomOrderMatching.Algebra.Tutte.Representation
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem historical_deletion_budget_verified
    (w : Edge V → ℝ) (hw : ∀ e, 0 ≤ w e) (K : ℕ → Graph V)
    (marks X : ℕ → Finset V) (charge : ℕ → ℝ) (n : ℕ)
    (hhost : ∀ i < n, K i ⊆ K (i+1))
    (hX : ∀ i < n, X i ⊆ marks i)
    (hmarks : ∀ i < n, marks (i+1) = marks i \ X i)
    (hcharge : ∀ i < n, charge i ≤
      opt w (K (i+1)) - opt w (deleteVertices (K (i+1)) (X i))) :
    (∑ i ∈ Finset.range n, charge i) + pathValue w (K 0) (marks 0) ≤
      2 * opt w (K n) :=
  historical_deletion_budget w K marks X charge n hhost
    (fun _ _ => pathValue_submodular_real _ _ hw) hX hmarks hcharge

theorem historical_phase_cut_transfer_verified
    (w : Edge V → ℕ) (A forced : Graph V) (K : ℕ → Graph V)
    (L IL IR : Finset V) (marks : ℕ → Finset V) (e : ℕ → Edge V)
    (selected : ℕ → Prop) [DecidablePred selected] (n : ℕ)
    (hAK : A ⊆ K 0) (hcross : Crosses A L)
    (hIL : IL ⊆ L) (hIR : IR ⊆ Finset.univ \ L) (hinit : marks 0 = IL ∪ IR)
    (hrun : ∀ i < n, K (i+1) = RandomOrderMatching.Phases.WeightedState.step w forced (K i) (e i))
    (hend : ∀ i < n, selected i → (e i).val ⊆ marks i)
    (hmarks : ∀ i < n, marks (i+1) =
      if selected i then marks i \ (e i).val else marks i) :
    opt (fun f => (w f : ℝ)) (deleteVertices A IL) +
      opt (fun f => (w f : ℝ)) (deleteVertices A IR) +
      (∑ i ∈ Finset.range n, if selected i then (w (e i) : ℝ) else 0) ≤
        2 * opt (fun f => (w f : ℝ)) (K n) :=
  historical_phase_cut_transfer w A forced K L IL IR marks e selected n
    hAK hcross hIL hIR hinit hrun
    (fun _ _ => pathValue_submodular_edge_nat _ _) hend hmarks

theorem PhaseWitness.score_le_final_verified {w : Edge V → ℕ} (P : PhaseWitness w) :
    P.score ≤ opt (fun e => (w e : ℝ)) (P.host P.length) :=
  P.score_le_final (fun _ _ => pathValue_submodular_edge_nat _ _)

theorem phase_profile_lift_verified {I : Type*} (w : Edge V → ℕ)
    (base output : Graph V) (P : I → PhaseWitness w)
    (hbase : base ⊆ output)
    (hphases : ∀ i, (P i).host (P i).length ⊆ output)
    (target : ℝ)
    (profile : target ≤ opt (fun e => (w e : ℝ)) base ∨
      ∃ i, target ≤ (P i).score) :
    ∃ M ⊆ output, Matching M ∧ target ≤ ∑ e ∈ M, (w e : ℝ) :=
  phase_profile_lift w base output P hbase hphases
    (fun _ _ _ => pathValue_submodular_edge_nat _ _) target profile

end RandomOrderMatching.Unfolding.PhaseLifting

#print axioms RandomOrderMatching.Unfolding.PhaseLifting.historical_deletion_budget_verified
#print axioms RandomOrderMatching.Unfolding.PhaseLifting.historical_phase_cut_transfer_verified
#print axioms RandomOrderMatching.Unfolding.PhaseLifting.phase_profile_lift_verified
