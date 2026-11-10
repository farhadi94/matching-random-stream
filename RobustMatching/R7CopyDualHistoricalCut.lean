import RobustMatching.R7CopyDualHistorical
import RobustMatching.R7GraphMarked

/-! The actual bipartite initial-cut witness is discharged using graph
component recoloring; only actual pathValue submodularity remains external. -/
noncomputable section
open scoped BigOperators

namespace RobustMatching.R7CopyDualHistorical
open RobustMatching.R2Cut RobustMatching.R7AlgebraPath
open RobustMatching.R6FableImportance RobustMatching.R7GraphBipartiteExchange
open RobustMatching.R6FableAlgebraSubmodular

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem historical_cut_deletion_budget
    (w : Edge V → ℝ) (A : Graph V) (K : ℕ → Graph V)
    (L IL IR : Finset V) (marks X : ℕ → Finset V) (charge : ℕ → ℝ) (n : ℕ)
    (hAK : A ⊆ K 0) (hcross : Crosses A L)
    (hIL : IL ⊆ L) (hIR : IR ⊆ Finset.univ \ L) (hinit : marks 0 = IL ∪ IR)
    (hhost : ∀ i < n, K i ⊆ K (i+1))
    (hsub : ∀ i < n, Submodular (pathValue w (K (i+1))))
    (hX : ∀ i < n, X i ⊆ marks i)
    (hmarks : ∀ i < n, marks (i+1) = marks i \ X i)
    (hcharge : ∀ i < n, charge i ≤
      opt w (K (i+1)) - opt w (deleteVertices (K (i+1)) (X i))) :
    opt w (deleteVertices A IL) + opt w (deleteVertices A IR) +
      (∑ i ∈ Finset.range n, charge i) ≤ 2 * opt w (K n) := by
  have hh := historical_deletion_budget w K marks X charge n hhost hsub hX hmarks hcharge
  have hi := RobustMatching.R7GraphMarked.deletion_optima_le_pathValue w hAK hcross hIL hIR
  rw [hinit] at hh
  linarith

theorem historical_phase_path_bound
    (w : Edge V → ℕ) (forced : Graph V) (K : ℕ → Graph V)
    (marks : ℕ → Finset V) (e : ℕ → Edge V) (selected : ℕ → Prop)
    [DecidablePred selected] (n : ℕ)
    (hrun : ∀ i < n, K (i+1) = R7WeightedPhase.step w forced (K i) (e i))
    (hsub : ∀ i < n, Submodular (pathValue (fun f => (w f : ℝ)) (K (i+1))))
    (hend : ∀ i < n, selected i → (e i).val ⊆ marks i)
    (hmarks : ∀ i < n, marks (i+1) =
      if selected i then marks i \ (e i).val else marks i) :
    pathValue (fun f => (w f : ℝ)) (K 0) (marks 0) +
      (∑ i ∈ Finset.range n, if selected i then (w (e i) : ℝ) else 0) ≤
        2 * opt (fun f => (w f : ℝ)) (K n) := by
  obtain ⟨p,hp,hval⟩ := pathValue_attained (fun f => (w f : ℝ)) (K 0) (marks 0)
  obtain ⟨h₁,h₂,hadm⟩ := (mem_feasiblePairs (K 0) (marks 0) p).mp hp
  rw [hval]
  exact historical_phase_certificate w forced K marks e selected n hrun hsub hend hmarks
    p.1 p.2 h₁ h₂ hadm

/-- Historical transfer for a fully defined original-weight phase, actual
bipartite initial support, and selected proposal arrivals. Neither closure
events, host growth, nor initial admissible matching witnesses are assumed. -/
theorem historical_phase_cut_transfer
    (w : Edge V → ℕ) (A forced : Graph V) (K : ℕ → Graph V)
    (L IL IR : Finset V) (marks : ℕ → Finset V) (e : ℕ → Edge V)
    (selected : ℕ → Prop) [DecidablePred selected] (n : ℕ)
    (hAK : A ⊆ K 0) (hcross : Crosses A L)
    (hIL : IL ⊆ L) (hIR : IR ⊆ Finset.univ \ L) (hinit : marks 0 = IL ∪ IR)
    (hrun : ∀ i < n, K (i+1) = R7WeightedPhase.step w forced (K i) (e i))
    (hsub : ∀ i < n, Submodular (pathValue (fun f => (w f : ℝ)) (K (i+1))))
    (hend : ∀ i < n, selected i → (e i).val ⊆ marks i)
    (hmarks : ∀ i < n, marks (i+1) =
      if selected i then marks i \ (e i).val else marks i) :
    opt (fun f => (w f : ℝ)) (deleteVertices A IL) +
      opt (fun f => (w f : ℝ)) (deleteVertices A IR) +
      (∑ i ∈ Finset.range n, if selected i then (w (e i) : ℝ) else 0) ≤
        2 * opt (fun f => (w f : ℝ)) (K n) := by
  have hh := historical_phase_path_bound w forced K marks e selected n hrun hsub hend hmarks
  have hi := RobustMatching.R7GraphMarked.deletion_optima_le_pathValue
    (fun f => (w f : ℝ)) hAK hcross hIL hIR
  rw [hinit] at hh
  linarith

end RobustMatching.R7CopyDualHistorical

#print axioms RobustMatching.R7CopyDualHistorical.historical_phase_cut_transfer
