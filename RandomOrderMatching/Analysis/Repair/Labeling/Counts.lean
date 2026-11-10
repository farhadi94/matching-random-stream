import RandomOrderMatching.Analysis.Repair.Labeling.Types
import RandomOrderMatching.Analysis.Profile.MomentRows

/-! Exact fiber counts for the semantic LP-to-typed-profile interface. -/
noncomputable section
open scoped BigOperators
open Classical

namespace RandomOrderMatching.Analysis.Repair.Labeling
open RandomOrderMatching.Analysis.Profile

variable {B U : Type*} [Fintype B] {q : ℕ}

theorem kindCount_eq_fiber_card (d : Coordinates B U q) (k : PairKind) :
    kindCount d k = (Fintype.card (PairFiber d k) : ℝ) := by
  simp [kindCount, PairFiber, Fintype.card_subtype]

end RandomOrderMatching.Analysis.Repair.Labeling
