import RobustMatching.R7ClosedRepairTypedLabeling
import RobustMatching.R7SupportFlowMapMomentRows

/-! Exact fiber counts for the semantic LP-to-typed-profile interface. -/
noncomputable section
open scoped BigOperators
open Classical

namespace RobustMatching.R7ClosedRepair.TypedLabeling
open RobustMatching.R7SupportFlowMap

variable {B U : Type*} [Fintype B] {q : ℕ}

theorem kindCount_eq_fiber_card (d : Coordinates B U q) (k : PairKind) :
    kindCount d k = (Fintype.card (PairFiber d k) : ℝ) := by
  simp [kindCount, PairFiber, Fintype.card_subtype]

end RobustMatching.R7ClosedRepair.TypedLabeling
