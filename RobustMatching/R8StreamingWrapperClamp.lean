import RobustMatching.R8StreamingWrapperCanonical
import RobustMatching.R8WeightWindowsProbability
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R8WeightWindows RobustMatching.R7ProbabilityRestriction
variable {V : Type*} [DecidableEq V]
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-- Clamp all queries before constructing the bounded copied alphabet. -/
def clippedWeight (w : Edge V → ℕ) (W : ℕ) : Edge V → ℕ := fun e => min (w e) W

theorem clippedWeight_le (w : Edge V → ℕ) (W : ℕ) (e : Edge V) :
    clippedWeight w W e ≤ W := Nat.min_le_right _ _

theorem clippedWeight_eq (w : Edge V → ℕ) (W : ℕ) (e : Edge V) (he : w e ≤ W) :
    clippedWeight w W e = w e := Nat.min_eq_left he

theorem clippedWeight_sum (w : Edge V → ℕ) (W : ℕ) (l : List (Edge V))
    (hw : ∀ e ∈ l, w e ≤ W) (M : Graph V) (hM : M ⊆ l.toFinset) :
    (∑ e ∈ M, (clippedWeight w W e : ℝ)) = ∑ e ∈ M, (w e : ℝ) := by
  apply Finset.sum_congr rfl
  intro e he
  rw [clippedWeight_eq w W e (hw e (List.mem_toFinset.mp (hM he)))]

/-- Preprocessing retains the underlying machine's state type and transitions. -/
def clampMachine (a : Machine V) (W : ℕ) : Machine V where
  State := a.State
  initial w := a.initial (clippedWeight w W)
  step w := a.step (clippedWeight w W)
  output w := a.output (clippedWeight w W)

theorem clampMachine_run (a : Machine V) (W : ℕ) (w : Edge V → ℕ)
    (l : List (Edge V)) :
    (clampMachine a W).run w l = a.run (clippedWeight w W) l := rfl

theorem clampMachine_answer (a : Machine V) (W : ℕ) (w : Edge V → ℕ)
    (l : List (Edge V)) :
    (clampMachine a W).answer w l = a.answer (clippedWeight w W) l := rfl

theorem clampMachine_valid (a : Machine V) (W : ℕ) (ha : a.Valid) :
    (clampMachine a W).Valid := fun w l => ha (clippedWeight w W) l

theorem clampMachine_good_iff (a : Machine V) (W : ℕ) (ha : a.Valid)
    (alpha : ℝ) (w : Edge V → ℕ) (l : List (Edge V))
    (hw : ∀ e ∈ l, w e ≤ W) :
    (clampMachine a W).Good alpha w l ↔ a.Good alpha (clippedWeight w W) l := by
  have ho := (ha (clippedWeight w W) l).2
  have hs := clippedWeight_sum w W l hw (a.answer (clippedWeight w W) l) ho
  unfold Machine.Good
  simp only [clampMachine_answer]
  constructor
  · intro h M hM hm
    rw [clippedWeight_sum w W l hw M hM,hs]
    exact h M hM hm
  · intro h M hM hm
    have hh := h M hM hm
    rwa [clippedWeight_sum w W l hw M hM,hs] at hh

/-- A domain-change lemma only: the separate bounded-weight approximation
remains an explicit input until the fixed-host probability proof is joined. -/
theorem clampMachine_contract_of_global_success (a : Machine V) (W : ℕ)
    (alpha delta : ℝ) (ha : a.Valid)
    (hs : ∀ (w : Edge V → ℕ) (l : List (Edge V)),
      (∀ e, w e ≤ W) → l.Nodup → (∀ e ∈ l, 1 ≤ w e) →
      permMean l (fun u => if a.Good alpha w u then 0 else 1) ≤ delta) :
    (clampMachine a W).Contract W alpha delta := by
  refine ⟨clampMachine_valid a W ha,?_⟩
  intro w l hnd hw
  have hh := hs (clippedWeight w W) l (clippedWeight_le w W) hnd (by
    intro e he
    rw [clippedWeight_eq w W e (hw e he).2]
    exact (hw e he).1)
  apply (R8WeightWindows.permMean_mono l _ _ ?_).trans hh
  intro u hu
  have hp : u.Perm l := List.mem_permutations'.mp hu
  have hwu : ∀ e ∈ u, w e ≤ W := fun e he => (hw e (hp.mem_iff.mp he)).2
  rw [clampMachine_good_iff a W ha alpha w u hwu]

variable [Fintype V]

def clampedBoundedOutput (w : Edge V → ℕ) (W L LU L0 : ℕ)
    (hW : 0 < W) (hL : 0 < L) (l : List (Edge V)) : Graph V :=
  finalBoundedOutput (clippedWeight w W) W L LU L0 (clippedWeight_le w W) hW hL l

theorem clampedBoundedOutput_valid (w : Edge V → ℕ) (W L LU L0 : ℕ)
    (hW : 0 < W) (hL : 0 < L) (l : List (Edge V)) :
    Matching (clampedBoundedOutput w W L LU L0 hW hL l) ∧
      clampedBoundedOutput w W L LU L0 hW hL l ⊆ l.toFinset :=
  finalBoundedOutput_valid_all _ _ _ _ _ _ _ _ _

theorem clampedBoundedOutput_weight (w : Edge V → ℕ) (W L LU L0 : ℕ)
    (hW : 0 < W) (hL : 0 < L) (l : List (Edge V)) (hw : ∀ e ∈ l,w e ≤ W) :
    (∑ e ∈ clampedBoundedOutput w W L LU L0 hW hL l,(clippedWeight w W e:ℝ)) =
      ∑ e ∈ clampedBoundedOutput w W L LU L0 hW hL l,(w e:ℝ) :=
  clippedWeight_sum w W l hw _ (clampedBoundedOutput_valid w W L LU L0 hW hL l).2

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.clampMachine_contract_of_global_success
#print axioms RobustMatching.R8StreamingWrapper.clampedBoundedOutput_weight
