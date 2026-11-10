import RobustMatching.R7WeightedPhaseAssemblyHistory
import RobustMatching.R7CopyDualGeneralCopies
import RobustMatching.R7CopyDualRefold

/-! The actual phase bank satisfies copied deletion transfer. Support
containment, all historical observations, and final matching domination
are derived from the original-label execution, not assumed as a bound. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7WeightedPhaseAssembly
open RobustMatching.R2Cut RobustMatching.R7WeightedPhase RobustMatching.R6FableImportance
open RobustMatching.Dual RobustMatching.R6FableSharpDualCopy
open RobustMatching.R7CopyDualGeneralBridge
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Full copied transfer for a concrete original-label phase. Parents of
selected copies need not be a matching and may overlap arbitrarily. -/
theorem concrete_phase_copied_bound
    (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (a c t : ℕ) (hac : a ≤ c) (hct : c ≤ t)
    (cut : Finset V) (W : ℕ) (E P : Finset (Left cut × Right cut))
    (hE : encode cut E ⊆ initial H eligible stream a)
    (hP : ∀ e ∈ encode cut P, e ∈ sharedBase H eligible stream ∨ e ∈ stream.drop t)
    (C1 C2 S : Finset ((Left cut × Fin W) × (Right cut × Fin W)))
    (hc1 : IsMatching C1) (hc2 : IsMatching C2) (hS : IsMatching S)
    (hs1 : ∀ e ∈ C1, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p)))
    (hs2 : ∀ e ∈ C2, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p)))
    (hsub : ∀ e ∈ S, R7CopyDual.parent e ∈ P)
    (hd1 : Disjoint (C1.image Prod.fst) (S.image Prod.fst))
    (hd2 : Disjoint (C2.image Prod.snd) (S.image Prod.snd))
    (hidx : ∀ e ∈ S, e.1.2.val+e.2.2.val+1=w (edgeOf cut (R7CopyDual.parent e))) :
    C1.card+C2.card+S.card ≤ 2 * natOpt w (phaseFinal w H eligible stream c) := by
  have hh := R7CopyDualGeneralCopies.historical_copied_matching_bound cut W w
    (phaseHost w H eligible stream c)
    (fun i j hij => phaseHost_mono w H eligible stream c hij) (stream.drop c).length E P
    (early_support_in_phase w H (encode cut E) eligible stream hac hE 0)
    (fun e he => phase_historical_closure w H eligible stream c e
      (repair_parent_initial_or_tested H eligible stream hct e (hP e he)))
    C1 C2 S hc1 hc2 hS hs1 hs2 hsub hd1 hd2 hidx
  rwa [phaseHost_terminal] at hh

/-- The copied deletion certificate is paid by the concrete matching
returned from the shared retained original graph. -/
theorem bank_copied_bound
    (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (a c t : ℕ)
    (hc : c ∈ activeCuts cuts stream) (hac : a ≤ c) (hct : c ≤ t)
    (cut : Finset V) (W : ℕ) (E P : Finset (Left cut × Right cut))
    (hE : encode cut E ⊆ initial H eligible stream a)
    (hP : ∀ e ∈ encode cut P, e ∈ sharedBase H eligible stream ∨ e ∈ stream.drop t)
    (C1 C2 S : Finset ((Left cut × Fin W) × (Right cut × Fin W)))
    (hc1 : IsMatching C1) (hc2 : IsMatching C2) (hS : IsMatching S)
    (hs1 : ∀ e ∈ C1, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p)))
    (hs2 : ∀ e ∈ C2, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p)))
    (hsub : ∀ e ∈ S, R7CopyDual.parent e ∈ P)
    (hd1 : Disjoint (C1.image Prod.fst) (S.image Prod.fst))
    (hd2 : Disjoint (C2.image Prod.snd) (S.image Prod.snd))
    (hidx : ∀ e ∈ S, e.1.2.val+e.2.2.val+1=w (edgeOf cut (R7CopyDual.parent e))) :
    (C1.card : ℝ)+C2.card+S.card ≤
      2 * ∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ) := by
  have hh := concrete_phase_copied_bound w H eligible stream a c t hac hct cut W E P hE hP
    C1 C2 S hc1 hc2 hS hs1 hs2 hsub hd1 hd2 hidx
  have hr : (C1.card : ℝ)+C2.card+S.card ≤
      2 * opt (fun e => (w e : ℝ)) (phaseFinal w H eligible stream c) := by
    rw [opt_eq_natOpt]
    exact_mod_cast hh
  have ho := phase_value_le_output w H eligible stream cuts c hc
  linarith

/-- Arbitrary retained copied base matchings refold inside the FULL shared
original base. This proves the base bound without q_initial >= b. -/
theorem bank_base_copy_bound
    (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ)
    (cut : Finset V) (W : ℕ) (E : Finset (Left cut × Right cut))
    (hE : encode cut E ⊆ sharedBase H eligible stream)
    (C : Finset ((Left cut × Fin W) × (Right cut × Fin W)))
    (hC : IsMatching C)
    (hs : ∀ e ∈ C, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p))) :
    (C.card : ℝ) ≤ ∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ) := by
  obtain ⟨M,hm,hME,hcard⟩ := R7CopyDual.copy_matching_refolds W E
    (fun p => w (edgeOf cut p)) C hC hs
  have hnat : (C.card : ℝ) ≤ ∑ p ∈ M, (w (edgeOf cut p) : ℝ) := by exact_mod_cast hcard
  have hopt := RobustMatching.Lower.weight_le_packingOpt Matching empty_matching
    (fun e => (w e : ℝ)) (encode_matching cut M hm) ((encode_mono cut hME).trans hE)
  rw [encode_sum] at hopt
  exact hnat.trans (hopt.trans (base_value_le_output w H eligible stream cuts))

end RobustMatching.R7WeightedPhaseAssembly
#print axioms RobustMatching.R7WeightedPhaseAssembly.bank_copied_bound
#print axioms RobustMatching.R7WeightedPhaseAssembly.bank_base_copy_bound
