import RobustMatching.R7SupportFlowMapCertificate

/-! Exact affine-arm choices for the two capped outside loads. The masks
are selected from the loads; an arbitrary affine arm would give an upper
bound and would be unsuitable for the graph-to-certificate argument. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate

def affineRefund {q} (data : ProfileData q) (t : OutsideType) (m : Fin 4)
    (L B : ℝ) : ℝ :=
  if t=.A then (if m.val % 2=1 then (inactive data : ℝ) else B)
  else (if m.val % 2=1 then (primaryCap data t : ℝ) else L)+
    (if m.val / 2 % 2=1 then 1 else B)

def cappedRefund {q} (data : ProfileData q) (t : OutsideType) (L B : ℝ) : ℝ :=
  if t=.A then min B (inactive data : ℝ)
  else min L (primaryCap data t : ℝ)+min B 1

def loadMask {q} (data : ProfileData q) (t : OutsideType) (L B : ℝ) : Fin 4 :=
  if t=.A then (if B ≤ (inactive data : ℝ) then 0 else 1)
  else if L ≤ (primaryCap data t : ℝ) then (if B ≤ 1 then 0 else 2)
  else if B ≤ 1 then 1 else 3

theorem loadMask_refund {q} (data : ProfileData q) (t : OutsideType) (L B : ℝ) :
    affineRefund data t (loadMask data t L B) L B = cappedRefund data t L B := by
  by_cases ht : t=.A
  · subst t
    by_cases hB : B ≤ (inactive data : ℝ)
    · simp [loadMask,affineRefund,cappedRefund,hB,min_eq_left hB]
    · simp [loadMask,affineRefund,cappedRefund,hB,min_eq_right (le_of_not_ge hB)]
  · by_cases hL : L ≤ (primaryCap data t : ℝ) <;> by_cases hB : B ≤ 1
    all_goals simp [loadMask,affineRefund,cappedRefund,ht,hL,hB,
      min_eq_left, min_eq_right, le_of_not_ge] <;> split_ifs <;> linarith

theorem loadMask_allowed {q} (data : ProfileData q) (i : Fin q) (t : OutsideType)
    (L B : ℝ)
    (hlow : t=.O → upper data i ≤ 1/2 → L ≤ 1 ∧ B ≤ 1) :
    outsideAllowed data (i,t,loadMask data t L B) := by
  cases t with
  | A => simp [outsideAllowed,loadMask]; split_ifs <;> norm_num
  | S => trivial
  | T => trivial
  | O =>
    intro h
    obtain ⟨hL,hB⟩ := hlow rfl h
    simp [loadMask,primaryCap,hL,hB]

theorem cappedRefund_mono {q} (data : ProfileData q) (t : OutsideType)
    {L L' B B' : ℝ} (hL : L ≤ L') (hB : B ≤ B') :
    cappedRefund data t L B ≤ cappedRefund data t L' B' := by
  unfold cappedRefund
  split_ifs
  · exact min_le_min hB le_rfl
  · exact add_le_add (min_le_min hL le_rfl) (min_le_min hB le_rfl)

/-- Grouping the chosen affine coefficients over the incidences of one
outside vertex gives exactly its capped load contribution. -/
theorem outside_affine_group {q} {C : Type*} [Fintype C]
    (data : ProfileData q) (i : Fin q) (t : OutsideType) (m : Fin 4)
    (centers : C → CenterClass q) (multiplicity : C → ℝ) (beta : ℝ) :
    (outsideCredit data (i,t,m) : ℝ)+
      (∑ c, multiplicity c*(edgeCredit data (centers c) (i,t,m) : ℝ))/beta =
    affineRefund data t m
      ((∑ c, multiplicity c*(primaryRate data (centers c).2 : ℝ))/
        (beta*(max data.cap (1-lower data i) : ℚ)))
      ((∑ c, multiplicity c*(secondaryRate data (centers c).2 : ℝ))/
        (beta*(max data.cap (1-lower data i) : ℚ)))/2 := by
  classical
  by_cases ht : t=.A
  · subst t
    fin_cases m <;>
      simp [outsideCredit,edgeCredit,affineRefund,Finset.sum_div, mul_div_assoc,
        ←Finset.sum_mul] <;> ring_nf <;>
      simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]
  · fin_cases m <;>
      simp [outsideCredit,edgeCredit,affineRefund,ht,Finset.sum_add_distrib,
        Finset.sum_div,mul_div_assoc,←Finset.sum_mul,mul_add] <;> ring_nf <;>
      simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]

end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.loadMask_refund
#print axioms RobustMatching.R7SupportFlowMap.loadMask_allowed
#print axioms RobustMatching.R7SupportFlowMap.outside_affine_group
