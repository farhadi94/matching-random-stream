import RobustMatching.R7CopyDualUnfold
import RobustMatching.R7CopyDualHistoricalCut

/-!
Two distinct transfer statements:
* an unconditional approximation-preserving bipartite unfolding reduction;
* a phase-certificate compiler on actual general graphs, with the existing
  marked-path submodularity theorem as its sole structural graph premise.
Neither statement asserts that ordinary random-order algorithms tolerate
the correlated copy blocks produced by unfolding.
-/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RobustMatching.R7CopyDualLifting

section Bipartite
open RobustMatching.Dual RobustMatching.R7CopyDual
open RobustMatching.R6FableSharpDualCopy
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem fullCopies_mono (W : ℕ) (w : L × R → ℕ)
    {M E : Finset (L × R)} (hME : M ⊆ E) :
    fullCopies W M w ⊆ fullCopies W E w := by
  classical
  intro f hf
  obtain ⟨_,hp,hi⟩ := Finset.mem_filter.mp hf
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hME hp,hi⟩

/-- Any approximate cardinality matching in the full bipartite unfolding
refolds to the same weighted approximation, using only retained parents.
The oracle contract quantifies over actual copy matchings, not weighted optima. -/
theorem bipartite_approximation_lift
    (W : ℕ) (E : Finset (L × R)) (w : L × R → ℕ)
    (hw : ∀ e ∈ E, w e ≤ W) (α : ℝ)
    (C : Finset ((L × Fin W) × (R × Fin W)))
    (hC : IsMatching C) (hCE : C ⊆ fullCopies W E w)
    (happrox : ∀ D ⊆ fullCopies W E w, IsMatching D → α * (D.card : ℝ) ≤ C.card) :
    ∃ M : Finset (L × R), IsMatching M ∧ M ⊆ C.image parent ∧ M ⊆ E ∧
      ∀ N ⊆ E, IsMatching N → α * (∑ e ∈ N, (w e : ℝ)) ≤ ∑ e ∈ M, (w e : ℝ) := by
  obtain ⟨M,hM,hMC,hweight⟩ := retained_copy_matching_refolds W w C hC
    (fun f hf => fullCopies_indices W E w f (hCE hf))
  have hME : M ⊆ E := by
    intro e he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp (hMC he)
    exact hfe ▸ fullCopies_parent W E w f (hCE hf)
  refine ⟨M,hM,hMC,hME,?_⟩
  intro N hNE hN
  have hc := happrox (fullCopies W N w) (fullCopies_mono W w hNE)
    (fullCopies_matching W N w hN)
  rw [fullCopies_card W N w (fun e he => hw e (hNE he))] at hc
  have hr : (C.card : ℝ) ≤ ∑ e ∈ M, (w e : ℝ) := by exact_mod_cast hweight
  simpa only [Nat.cast_sum] using hc.trans hr

end Bipartite

section Phases
open RobustMatching.R2Cut RobustMatching.R7AlgebraPath
open RobustMatching.R6FableImportance RobustMatching.R7GraphBipartiteExchange
open RobustMatching.R6FableAlgebraSubmodular RobustMatching.R7CopyDualHistorical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Data and causal evolution of one actual weighted phase. The analytic cut
and marks certify the trajectory; the update rule does not read them. -/
structure PhaseWitness (w : Edge V → ℕ) where
  initialSupport : Graph V
  forced : Graph V
  host : ℕ → Graph V
  cut : Finset V
  leftMarks : Finset V
  rightMarks : Finset V
  marks : ℕ → Finset V
  arrival : ℕ → Edge V
  selected : ℕ → Prop
  selectedDecidable : DecidablePred selected
  length : ℕ
  support_subset : initialSupport ⊆ host 0
  support_crosses : Crosses initialSupport cut
  left_subset : leftMarks ⊆ cut
  right_subset : rightMarks ⊆ Finset.univ \ cut
  initial_marks : marks 0 = leftMarks ∪ rightMarks
  actual_step : ∀ i < length,
    host (i+1) = R7WeightedPhase.step w forced (host i) (arrival i)
  selected_inside : ∀ i < length, selected i → (arrival i).val ⊆ marks i
  release_marks : ∀ i < length, marks (i+1) =
    @ite _ (selected i) (selectedDecidable i) (marks i \ (arrival i).val) (marks i)

def PhaseWitness.score {w : Edge V → ℕ} (P : PhaseWitness w) : ℝ :=
  (opt (fun e => (w e : ℝ)) (deleteVertices P.initialSupport P.leftMarks) +
   opt (fun e => (w e : ℝ)) (deleteVertices P.initialSupport P.rightMarks) +
   ∑ i ∈ Finset.range P.length,
     @ite ℝ (P.selected i) (P.selectedDecidable i) (w (P.arrival i) : ℝ) 0) / 2

theorem PhaseWitness.score_le_final {w : Edge V → ℕ} (P : PhaseWitness w)
    (hsub : ∀ i < P.length,
      Submodular (pathValue (fun e => (w e : ℝ)) (P.host (i+1)))) :
    P.score ≤ opt (fun e => (w e : ℝ)) (P.host P.length) := by
  letI := P.selectedDecidable
  have hh := historical_phase_cut_transfer w P.initialSupport P.forced P.host
    P.cut P.leftMarks P.rightMarks P.marks P.arrival P.selected P.length
    P.support_subset P.support_crosses P.left_subset P.right_subset P.initial_marks
    P.actual_step hsub P.selected_inside P.release_marks
  unfold PhaseWitness.score
  linarith

/-- Any scalar profile proved from the base value or one of the historical
phase scores yields an actual output matching with the SAME target value.
The profile is supplied as a separate certificate, not inferred from tests. -/
theorem phase_profile_lift {I : Type*} (w : Edge V → ℕ)
    (base output : Graph V) (P : I → PhaseWitness w)
    (hbase : base ⊆ output)
    (hphases : ∀ i, (P i).host (P i).length ⊆ output)
    (hsub : ∀ i, ∀ t < (P i).length,
      Submodular (pathValue (fun e => (w e : ℝ)) ((P i).host (t+1))))
    (target : ℝ)
    (profile : target ≤ opt (fun e => (w e : ℝ)) base ∨
      ∃ i, target ≤ (P i).score) :
    ∃ M ⊆ output, Matching M ∧ target ≤ ∑ e ∈ M, (w e : ℝ) := by
  have hu : target ≤ opt (fun e => (w e : ℝ)) output := by
    rcases profile with hb | ⟨i,hi⟩
    · exact hb.trans (RobustMatching.Lower.packingOpt_mono Matching empty_matching
        (fun e => (w e : ℝ)) hbase)
    · exact (hi.trans ((P i).score_le_final (hsub i))).trans
        (RobustMatching.Lower.packingOpt_mono Matching empty_matching
          (fun e => (w e : ℝ)) (hphases i))
  obtain ⟨M,hMO,hM,hval⟩ := RobustMatching.Lower.packingOpt_attained Matching
    empty_matching (fun e => (w e : ℝ)) output
  exact ⟨M,hMO,hM,by simpa only [opt,hval] using hu⟩

/-- Already-retained proposals can be inserted as analysis-only initial
events; the actual stored graph does not change. -/
theorem phase_step_of_mem (w : Edge V → ℕ) (forced G : Graph V)
    (e : Edge V) (he : e ∈ G) : R7WeightedPhase.step w forced G e = G := by
  unfold R7WeightedPhase.step
  split_ifs <;> simp [Finset.insert_eq_of_mem he]

/-- The canonical phase has a deterministic record bound at every prefix.
This uses actual integer optimum increments, not an expected space claim. -/
theorem phase_record_cap (w : Edge V → ℕ) (forced initial : Graph V)
    (arrivals : List (Edge V)) (vertices : Finset V) (W : ℕ)
    (hw : ∀ e ∈ initial ∪ arrivals.toFinset, w e ≤ W)
    (hv : ∀ e ∈ initial ∪ arrivals.toFinset, e.val ⊆ vertices) :
    (R7WeightedPhase.run w forced initial arrivals \ forced).card ≤
      (initial \ forced).card + W * (vertices.card / 2) := by
  have hs := R7WeightedPhase.run_subset w forced initial arrivals
  have hb := R7WeightedPhase.natOpt_vertex_bound w
    (R7WeightedPhase.run w forced initial arrivals) vertices W
    (fun e he => hw e (hs he)) (fun e he => hv e (hs he))
  have hr := R7WeightedPhase.run_record_bound w forced initial arrivals
  omega

end Phases
end RobustMatching.R7CopyDualLifting

#print axioms RobustMatching.R7CopyDualLifting.bipartite_approximation_lift
#print axioms RobustMatching.R7CopyDualLifting.phase_profile_lift
#print axioms RobustMatching.R7CopyDualLifting.phase_record_cap
