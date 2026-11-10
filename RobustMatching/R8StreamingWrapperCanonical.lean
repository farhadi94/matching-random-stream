import RobustMatching.R8StreamingWrapperValidity
import RobustMatching.R8AcquisitionCanonical
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R8Acquisition
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

def finalScaleConfig (W L Q cap M : ℕ) (hW : 0 < W) (hL : 0 < L) : Config :=
  finalAcquisitionConfig W L (max 1 (epochLength Q M)) cap hW hL
    (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _))

theorem finalScaleConfig_eq (W L Q cap M : ℕ) (hW : 0 < W) (hL : 0 < L) :
    let seed := finalAcquisitionConfig W L 1 0 hW hL (by decide)
    finalScaleConfig W L Q cap M hW hL=
      configForScale seed.beta seed.lower cap Q M seed.beta_pos seed.lower_gap := rfl

theorem finalScaleConfig_threshold (W L Q cap M : ℕ) (hW : 0 < W) (hL : 0 < L) :
    ((finalScaleConfig W L Q cap M hW hL).lower:ℝ)=
      (1-(10:ℝ)^(-9:ℤ))*((finalScaleConfig W L Q cap M hW hL).beta:ℝ) :=
  final_lower_exact W L _ cap hW hL _

def canonicalBoundedOutput (w : Edge V→ℕ) (W L LU L0 : ℕ) (hw : ∀e,w e ≤ W)
    (hW : 0 < W) (hL : 0 < L) (fallback : Edge V) (l : List (Edge V)) : Graph V :=
  let seed := finalAcquisitionConfig W L 1 0 hW hL (by decide)
  let Q := acquisitionBudget (Fintype.card (V×Fin W)) seed.beta
  let model := canonicalBatchModel W w hw fallback
  boundedIntegerOutput (Fintype.card V) Q (fullCapacity (Fintype.card V) Q W L0) w
    (fun M => finalScaleConfig W L Q (copiedCapacity Q W LU) M hW hL) model l

theorem canonicalBoundedOutput_eq_configured (w : Edge V→ℕ) (W L LU L0 : ℕ)
    (hw : ∀e,w e ≤ W) (hW : 0 < W) (hL : 0 < L) (fallback : Edge V) (l : List (Edge V)) :
    let seed := finalAcquisitionConfig W L 1 0 hW hL (by decide)
    canonicalBoundedOutput w W L LU L0 hw hW hL fallback l=
      configuredBoundedOutput w seed.beta seed.lower LU L0 seed.beta_pos seed.lower_gap
        (canonicalBatchModel W w hw fallback) l := rfl

/-- Total final bounded-integer algorithm. The canonical unfolding and final
acquisition threshold are fixed here, rather than supplied as unproved models.
If the vertex universe has no edge, the returned matching is empty. -/
def finalBoundedOutput (w : Edge V→ℕ) (W L LU L0 : ℕ) (hw : ∀e,w e ≤ W)
    (hW : 0 < W) (hL : 0 < L) (l : List (Edge V)) : Graph V :=
  if h : Nonempty (Edge V) then
    canonicalBoundedOutput w W L LU L0 hw hW hL (Classical.choice h) l
  else ∅

theorem finalBoundedOutput_valid (w : Edge V→ℕ) (W L LU L0 : ℕ) (hw : ∀e,w e ≤ W)
    (hW : 0 < W) (hL : 0 < L) (l : List (Edge V)) (hnd : l.Nodup) :
    Matching (finalBoundedOutput w W L LU L0 hw hW hL l) ∧
      finalBoundedOutput w W L LU L0 hw hW hL l⊆l.toFinset := by
  unfold finalBoundedOutput
  split_ifs with h
  · rw [canonicalBoundedOutput_eq_configured]
    exact configured_output_valid w _ _ LU L0 _ _ _ l hnd
  · simp [Matching]

theorem finalBoundedOutput_valid_all (w : Edge V→ℕ) (W L LU L0 : ℕ) (hw : ∀e,w e ≤ W)
    (hW : 0 < W) (hL : 0 < L) (l : List (Edge V)) :
    Matching (finalBoundedOutput w W L LU L0 hw hW hL l) ∧
      finalBoundedOutput w W L LU L0 hw hW hL l⊆l.toFinset := by
  unfold finalBoundedOutput
  split_ifs with h
  · rw [canonicalBoundedOutput_eq_configured]
    exact configured_output_valid_all w _ _ LU L0 _ _ _ l
  · simp [Matching]

theorem canonical_copied_vertex_count (W : ℕ) :
    Fintype.card (V×Fin W)=Fintype.card V*W := by simp

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.finalBoundedOutput_valid
#print axioms RobustMatching.R8StreamingWrapper.finalScaleConfig_threshold

#print axioms RobustMatching.R8StreamingWrapper.finalBoundedOutput_valid_all
