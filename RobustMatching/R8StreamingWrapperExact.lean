import RobustMatching.R8StreamingWrapperMachine
import RobustMatching.R8StreamingWrapperPermutation
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R8Acquisition RobustMatching.R8WeightWindows
open RobustMatching.R7WeightedPhaseAssembly RobustMatching.R7WeightedPhase RobustMatching.R6FableImportance
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

theorem finalBoundedOutput_full_exact (w : Edge V → ℕ) (W L LU L0 : ℕ)
    (hw : ∀ e,w e ≤ W) (hW : 0 < W) (hL : 0 < L) (l : List (Edge V))
    (hlen : l.length ≤ fullCapacity (Fintype.card V) (canonicalBudget V W L) W L0) :
    finalBoundedOutput w W L LU L0 hw hW hL l=decode w l.toFinset := by
  unfold finalBoundedOutput
  split_ifs with h
  · unfold canonicalBoundedOutput
    apply boundedInteger_full_exact
    exact hlen
  · have he : l=[] := by
      cases l with
      | nil => rfl
      | cons e es => exact (h ⟨e⟩).elim
    subst l
    apply Eq.symm
    apply Finset.Subset.antisymm _ (Finset.empty_subset _)
    intro e he
    exact (h ⟨e⟩).elim

theorem canonicalMachine_good_full (W L LU L0 : ℕ) (hW : 0 < W) (hL : 0 < L)
    (alpha : ℝ) (ha : alpha ≤ 1) (w : Edge V → ℕ) (l : List (Edge V))
    (hw : ∀ e ∈ l,w e ≤ W)
    (hlen : l.length ≤ fullCapacity (Fintype.card V) (canonicalBudget V W L) W L0) :
    (canonicalMachine (V:=V) W L LU L0 hW hL).Good alpha w l := by
  intro M hM hm
  have ho := (canonicalMachine_valid (V:=V) W L LU L0 hW hL) w l
  rw [canonicalMachine_answer]
  rw [←clampedBoundedOutput_weight w W L LU L0 hW hL l hw]
  unfold clampedBoundedOutput
  rw [finalBoundedOutput_full_exact _ _ _ _ _ _ _ _ l hlen,decode_real_weight,opt_eq_natOpt]
  have hb : (∑ e ∈ M,(clippedWeight w W e:ℝ)) ≤
      (natOpt (clippedWeight w W) l.toFinset:ℝ) := by
    exact_mod_cast matching_weight_le_natOpt (clippedWeight w W) hM hm
  rw [clippedWeight_sum w W l hw M hM] at hb
  exact (mul_le_of_le_one_left (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) ha).trans hb

theorem canonicalMachine_full_failure_zero (W L LU L0 : ℕ)
    (hW : 0 < W) (hL : 0 < L) (alpha : ℝ) (ha : alpha ≤ 1)
    (w : Edge V → ℕ) (l : List (Edge V)) (hw : ∀ e ∈ l,w e ≤ W)
    (hlen : l.length ≤ fullCapacity (Fintype.card V) (canonicalBudget V W L) W L0) :
    R7ProbabilityRestriction.permMean l (fun u =>
      if (canonicalMachine (V:=V) W L LU L0 hW hL).Good alpha w u then 0 else 1)=0 := by
  unfold R7ProbabilityRestriction.permMean
  have hs : (l.permutations'.map (fun u =>
      if (canonicalMachine (V:=V) W L LU L0 hW hL).Good alpha w u then (0:ℝ) else 1)).sum=0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
    have hp := List.mem_permutations'.mp hu
    rw [if_pos (canonicalMachine_good_full W L LU L0 hW hL alpha ha w u
      (fun e he => hw e (hp.mem_iff.mp he)) (by rw [hp.length_eq]; exact hlen))]
  rw [hs,zero_div]

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.canonicalMachine_full_failure_zero
