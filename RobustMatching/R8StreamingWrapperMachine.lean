import RobustMatching.R8StreamingWrapperClamp
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R8Acquisition RobustMatching.R8WeightWindows
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

def canonicalBudget (V : Type*) [Fintype V] (W L : ℕ) : ℕ :=
  acquisitionBudget (Fintype.card (V×Fin W)) (10^30*W*L)

/-- The final bounded-range streaming machine. Clamping is part of the
machine itself; there is no global bound assumption on its input function.
All scale copies exist at initialization, and each step consumes one edge. -/
def canonicalMachine (W L LU L0 : ℕ) (hW : 0 < W) (hL : 0 < L) : Machine V where
  State := OuterState V (LocalState (State (V×Fin W)) V) (Fintype.card V)
    (canonicalBudget V W L)
  initial _ := outerInit _ _ (fun _ => acquiredLocalInit)
  step w := if h : Nonempty (Edge V) then
    outerStep _ _ (fullCapacity (Fintype.card V) (canonicalBudget V W L) W L0)
      (fun M => acquiredLocalStep (clippedWeight w W)
        (finalScaleConfig W L (canonicalBudget V W L)
          (copiedCapacity (canonicalBudget V W L) W LU) M hW hL)
        (canonicalBatchModel W (clippedWeight w W) (clippedWeight_le w W) (Classical.choice h)))
    else fun s _ => s
  output w := if _h : Nonempty (Edge V) then
    outerOutput _ _ (clippedWeight w W) (fun _ => localAnswer (clippedWeight w W))
    else fun _ => ∅

theorem canonicalMachine_answer (W L LU L0 : ℕ) (hW : 0 < W) (hL : 0 < L)
    (w : Edge V → ℕ) (l : List (Edge V)) :
    (canonicalMachine W L LU L0 hW hL).answer w l =
      clampedBoundedOutput w W L LU L0 hW hL l := by
  by_cases h : Nonempty (Edge V)
  · simp only [Machine.answer,Machine.run,canonicalMachine,dif_pos h,if_pos h,
      clampedBoundedOutput,finalBoundedOutput,dif_pos h]
    rfl
  · simp only [Machine.answer,canonicalMachine,if_neg h,
      clampedBoundedOutput,finalBoundedOutput,dif_neg h]

theorem canonicalMachine_valid (W L LU L0 : ℕ) (hW : 0 < W) (hL : 0 < L) :
    (canonicalMachine (V:=V) W L LU L0 hW hL).Valid := by
  intro w l
  rw [canonicalMachine_answer]
  exact clampedBoundedOutput_valid w W L LU L0 hW hL l

/-- The all-benchmark local success obligation in exactly the form required
by the arbitrary-weight compiler. This theorem identifies the remaining
probability obligation; it does not assume success for the final theorem. -/
theorem canonicalMachine_contract_of_success (W L LU L0 : ℕ)
    (hW : 0 < W) (hL : 0 < L) (alpha delta : ℝ)
    (hs : ∀ (w : Edge V → ℕ) (l : List (Edge V)), l.Nodup →
      (∀ e ∈ l, 1 ≤ w e ∧ w e ≤ W) →
      RobustMatching.R7ProbabilityRestriction.permMean l (fun u =>
        if ∀ M : Graph V, M ⊆ u.toFinset → Matching M →
          alpha*(∑ e ∈ M,(w e:ℝ)) ≤
            ∑ e ∈ clampedBoundedOutput w W L LU L0 hW hL u,(w e:ℝ)
        then 0 else 1) ≤ delta) :
    (canonicalMachine (V:=V) W L LU L0 hW hL).Contract W alpha delta := by
  refine ⟨canonicalMachine_valid W L LU L0 hW hL,?_⟩
  intro w l hnd hw
  simpa only [Machine.Good,canonicalMachine_answer] using hs w l hnd hw

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.canonicalMachine_answer
#print axioms RobustMatching.R8StreamingWrapper.canonicalMachine_valid
