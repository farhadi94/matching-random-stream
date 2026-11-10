import RobustMatching.R7AlgebraPathValue
import RobustMatching.R7WeightedPhaseState

/-!
Historical deletion prices for actual nested weighted graphs.

The only structural input is submodularity of the graph-defined marked-path
value. Its generic weighted Tutte interpretation is still a separate formal
dependency. Host monotonicity, the changing-host telescope, and the closure
implication below are proved here, not assumed.
-/
noncomputable section
open scoped BigOperators

namespace RobustMatching.R7CopyDualHistorical
open RobustMatching.R2Cut RobustMatching.R7AlgebraPath
open RobustMatching.R6FableImportance
open RobustMatching.R6FableAlgebraSubmodular

variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

theorem pathValue_host_mono (w : Edge V → ℝ) {G H : Graph V}
    (hGH : G ⊆ H) (marks : Finset V) :
    pathValue w G marks ≤ pathValue w H marks := by
  obtain ⟨p, hp, hv⟩ := pathValue_attained w G marks
  obtain ⟨h₁, h₂, hadm⟩ := (mem_feasiblePairs G marks p).mp hp
  rw [hv]
  exact pairWeight_le_pathValue w (h₁.trans hGH) (h₂.trans hGH) hadm

theorem pathValue_release (w : Edge V → ℝ) (G : Graph V)
    (hsub : Submodular (pathValue w G))
    (marks X : Finset V) (hX : X ⊆ marks) :
    opt w G - opt w (deleteVertices G X) ≤
      pathValue w G (marks \ X) - pathValue w G marks := by
  exact release_gain (pathValue w G) hsub (opt w G)
    (opt w (deleteVertices G X)) (pathValue_empty w G) marks X hX
    (pathValue_one_set_upper w G X)

/-- The host used for an event is the post-step host `K (i+1)`.
The released set need not have size two, and strict host growth is unnecessary. -/
theorem historical_deletion_budget
    (w : Edge V → ℝ) (K : ℕ → Graph V)
    (marks X : ℕ → Finset V) (charge : ℕ → ℝ) (n : ℕ)
    (hhost : ∀ i < n, K i ⊆ K (i+1))
    (hsub : ∀ i < n, Submodular (pathValue w (K (i+1))))
    (hX : ∀ i < n, X i ⊆ marks i)
    (hmarks : ∀ i < n, marks (i+1) = marks i \ X i)
    (hcharge : ∀ i < n, charge i ≤
      opt w (K (i+1)) - opt w (deleteVertices (K (i+1)) (X i))) :
    (∑ i ∈ Finset.range n, charge i) + pathValue w (K 0) (marks 0) ≤
      2 * opt w (K n) := by
  have hstep : ∀ i < n, charge i + pathValue w (K i) (marks i) ≤
      pathValue w (K (i+1)) (marks (i+1)) := by
    intro i hi
    have hm := pathValue_host_mono w (hhost i hi) (marks i)
    have hr := pathValue_release w (K (i+1)) (hsub i hi)
      (marks i) (X i) (hX i hi)
    rw [hmarks i hi]
    linarith [hcharge i hi]
  have htel : ∀ k ≤ n,
      (∑ i ∈ Finset.range k, charge i) + pathValue w (K 0) (marks 0) ≤
        pathValue w (K k) (marks k) := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hp := ih (by omega)
      have hs := hstep k hk'
      rw [Finset.sum_range_succ]
      simpa only [Nat.succ_eq_add_one] using (by linarith :
        (∑ i ∈ Finset.range k, charge i) + charge k +
          pathValue w (K 0) (marks 0) ≤ pathValue w (K (k+1)) (marks (k+1)))
  have hupper := pathValue_antitone_marks w (K n)
    (Finset.empty_subset (marks n))
  rw [pathValue_empty] at hupper
  exact (htel n le_rfl).trans hupper

theorem closed_edge_price (w : Edge V → ℝ) (G : Graph V) (e : Edge V)
    (hclosed : opt w (insert e G) = opt w G) :
    w e ≤ opt w G - opt w (deleteVertices G e.val) := by
  have hi : w e + opt w (avoid G e) ≤ opt w G := by
    rw [opt_insert] at hclosed
    exact (le_max_right _ _).trans_eq hclosed
  have hd : avoid G e = deleteVertices G e.val := by
    ext f
    simp [avoid, deleteVertices]
  rw [hd] at hi
  linarith

/-- Actual original-edge closure events and actual initial matching witnesses.
This includes retained edges, since insertion into their post-step host is idle. -/
theorem historical_closed_edges_bound
    (w : Edge V → ℝ) (K : ℕ → Graph V)
    (marks : ℕ → Finset V) (e : ℕ → Edge V) (n : ℕ)
    (hhost : ∀ i < n, K i ⊆ K (i+1))
    (hsub : ∀ i < n, Submodular (pathValue w (K (i+1))))
    (hend : ∀ i < n, (e i).val ⊆ marks i)
    (hmarks : ∀ i < n, marks (i+1) = marks i \ (e i).val)
    (hclosed : ∀ i < n, opt w (insert (e i) (K (i+1))) = opt w (K (i+1)))
    (N₁ N₂ : Graph V) (hN₁ : N₁ ⊆ K 0) (hN₂ : N₂ ⊆ K 0)
    (hadm : Admissible N₁ N₂ (marks 0)) :
    pairWeight w (N₁,N₂) + (∑ i ∈ Finset.range n, w (e i)) ≤
      2 * opt w (K n) := by
  have hh := historical_deletion_budget w K marks (fun i => (e i).val)
    (fun i => w (e i)) n hhost hsub hend hmarks
    (fun i hi => closed_edge_price w (K (i+1)) (e i) (hclosed i hi))
  have hp := pairWeight_le_pathValue w hN₁ hN₂ hadm
  linarith

/-- Both retained and rejected originals are closed in their post-step host.
The rule may force arbitrary CURRENT labels; their zero gains cause no issue. -/
theorem phase_step_closed (w : Edge V → ℕ) (forced G : Graph V) (e : Edge V) :
    opt (fun f => (w f : ℝ)) (insert e (R7WeightedPhase.step w forced G e)) =
      opt (fun f => (w f : ℝ)) (R7WeightedPhase.step w forced G e) := by
  have he : insert e (R7WeightedPhase.step w forced G e) = insert e G := by
    unfold R7WeightedPhase.step
    split_ifs <;> simp
  rw [he]
  simp only [R7WeightedPhase.opt_eq_natOpt, R7WeightedPhase.natOpt_step]

/-- An actual original-weight phase with any chosen matching of tested
proposals. The selected labels are encoded by their disjoint remaining marks;
unselected arrivals release no marks and receive zero charge. -/
theorem historical_phase_certificate
    (w : Edge V → ℕ) (forced : Graph V) (K : ℕ → Graph V)
    (marks : ℕ → Finset V) (e : ℕ → Edge V) (selected : ℕ → Prop)
    [DecidablePred selected] (n : ℕ)
    (hrun : ∀ i < n, K (i+1) = R7WeightedPhase.step w forced (K i) (e i))
    (hsub : ∀ i < n, Submodular (pathValue (fun f => (w f : ℝ)) (K (i+1))))
    (hend : ∀ i < n, selected i → (e i).val ⊆ marks i)
    (hmarks : ∀ i < n, marks (i+1) =
      if selected i then marks i \ (e i).val else marks i)
    (N₁ N₂ : Graph V) (hN₁ : N₁ ⊆ K 0) (hN₂ : N₂ ⊆ K 0)
    (hadm : Admissible N₁ N₂ (marks 0)) :
    pairWeight (fun f => (w f : ℝ)) (N₁,N₂) +
      (∑ i ∈ Finset.range n, if selected i then (w (e i) : ℝ) else 0) ≤
        2 * opt (fun f => (w f : ℝ)) (K n) := by
  let wr : Edge V → ℝ := fun f => (w f : ℝ)
  let X : ℕ → Finset V := fun i => if selected i then (e i).val else ∅
  have hhost : ∀ i < n, K i ⊆ K (i+1) := by
    intro i hi
    rw [hrun i hi]
    exact R7WeightedPhase.subset_step w forced (K i) (e i)
  have hx : ∀ i < n, X i ⊆ marks i := by
    intro i hi
    by_cases hs : selected i
    · simpa [X, hs] using hend i hi hs
    · simp [X, hs]
  have hm : ∀ i < n, marks (i+1) = marks i \ X i := by
    intro i hi
    rw [hmarks i hi]
    by_cases hs : selected i <;> simp [X, hs]
  have hc : ∀ i < n, (if selected i then (w (e i) : ℝ) else 0) ≤
      opt wr (K (i+1)) - opt wr (deleteVertices (K (i+1)) (X i)) := by
    intro i hi
    by_cases hs : selected i
    · have hp := closed_edge_price wr (K (i+1)) (e i) (by
        rw [hrun i hi]
        exact phase_step_closed w forced (K i) (e i))
      simpa [X, hs, wr] using hp
    · simp [X, hs, deleteVertices]
  have hh := historical_deletion_budget wr K marks X
    (fun i => if selected i then (w (e i) : ℝ) else 0) n hhost hsub hx hm hc
  have hp := pairWeight_le_pathValue wr hN₁ hN₂ hadm
  dsimp [wr] at hh hp
  linarith

end RobustMatching.R7CopyDualHistorical

#print axioms RobustMatching.R7CopyDualHistorical.historical_deletion_budget
#print axioms RobustMatching.R7CopyDualHistorical.historical_closed_edges_bound
#print axioms RobustMatching.R7CopyDualHistorical.historical_phase_certificate
