import RobustMatching.R8RepairProbabilityLocalEvents
import RobustMatching.R8RepairProbabilityAggregateFibers
import RobustMatching.R7ClosedRepairTypedWeights

/-! Construct the probability input from actual capped reference incidences
and the one original-parent multiplicity bound. No local stochastic premises
or independent-copy assumptions are supplied to this construction. -/
noncomputable section
open Classical
open scoped BigOperators
namespace RobustMatching.R8RepairProbability
open R7ClosedRepair.Typed R1Gate
variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]

def referenceLocalData
    (p : Parents B G M J R) (b0 : B)
    (H : Centers G M P I J→Outsides R M G U→Prop)
    (sideC : Centers G M P I J→Bool) (sideO : Outsides R M G U→Bool)
    (hcross : ∀c x,H c x→sideC c≠sideO x)
    (β : ℝ) (a : Outsides R M G U→ℝ) (dc : Centers G M P I J→ℝ)
    (hs : SupportData (fun x c=>H c x) β a dc)
    (κ : ℕ) (hk : 0<κ) (hblock : ∀b,originalMultiplicity p b≤κ) :
    LocalData (B:=B) (G:=G) (M:=M) (P:=P) (I:=I) (J:=J) (R:=R) (U:=U) where
  parents := p
  fallback := b0
  H := H
  sideC := sideC
  sideO := sideO
  w := referenceWeight (fun x c=>H c x) β (1/100) a
  d := fun x=>max (1/100) (1-a x)
  beta := β
  kappa := κ
  beta_pos := hs.beta_pos
  kappa_pos := hk
  nonneg := referenceWeight_nonneg _ a hs.beta_pos (by norm_num)
  crossing := hcross
  supported := referenceWeight_supported _ _ _ _
  row_capacity := referenceWeight_row_capacity _ a dc hs
  denominator := fun _=>le_max_left _ _
  edge_weight := by
    intro c x
    unfold referenceWeight R7SupportFlow.cappedWeight
    split_ifs
    · rfl
    · exact le_of_lt (one_div_pos.mpr (mul_pos hs.beta_pos
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100) (le_max_left _ _))))
  column_mass := by
    intro x
    rw [referenceWeight_column_exact _ a dc hs (by norm_num)]
    exact div_le_div_of_nonneg_right (le_of_lt (hs.degree_lt_one x)) (by positivity)
  row_fibers := local_receiver_fibers_le p b0 κ hblock H sideO
  column_fibers := local_sender_fibers_le p b0 κ hblock H sideO

end RobustMatching.R8RepairProbability
