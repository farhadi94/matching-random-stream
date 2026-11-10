import RobustMatching.R7ReductionCertificateBounds
import RobustMatching.R7ReductionCertificateNumericCross
import RobustMatching.R7ReductionCertificateNumericPairs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace RobustMatching.R7ReductionCertificate.Concrete
open RobustMatching.R7ReductionCertificate

theorem cross_slack_formula (c : CenterClass 152) (x : OutsideClass 152) :
    intSlack grid dualDenominator dualEqNumerator dualLeNumerator (.cross c x) =
    -((centerPrice c+outsidePrice x)*(1000000*denominator grid x)+
      dualLeNumerator .phase*(25600*edgeInt (representative c.2) x)) := by
  have he : edgeInt (representative c.2) x = edgeInt c x := rfl
  rw [he]
  unfold intSlack intCost scale eqIntDot leIntDot centerPrice outsidePrice
  ring

theorem internal_slack_formula (c e : CenterClass 152) :
    intSlack grid dualDenominator dualEqNumerator dualLeNumerator (.internal c e) =
    -(centerPrice c+centerPrice e+dualLeNumerator .mass) := by
  unfold intSlack intCost scale eqIntDot leIntDot centerPrice
  ring

theorem all_integer_columns (c : Column 152) (hc : allowedInt grid c) :
    0 ≤ intSlack grid dualDenominator dualEqNumerator dualLeNumerator c := by
  cases c with
  | center c => exact center_slacks c
  | outside x => exact outside_slacks x hc
  | cross c x =>
    rcases hc with ⟨hx,hh⟩
    have hb := center_partner_bound c x.1 (by simpa [gLower,grid,add_comm] using hh)
    have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ 1000000*denominator grid x by
      have hp := denominator_pos grid x
      positivity)
    have hbudget := cross_budget c.2 x hx
    rw [cross_slack_formula]
    nlinarith
  | internal c e =>
    rcases hc with ⟨_,hh⟩
    have hb := all_partner_bound e c.1 (by simpa [gLower,grid] using hh)
    have hbudget := internal_budget c
    rw [internal_slack_formula]
    omega
  | root x y =>
    rcases x with ⟨i,t,k⟩
    rcases y with ⟨j,u,l⟩
    rcases hc with ⟨_,_,ht,hu,_,hh⟩
    dsimp at ht hu
    subst t
    subst u
    have hb := root_partner_bound i j l (by simpa [gUpper,grid] using hh)
    have hbudget := root_budget i k
    simp only [intSlack,intCost,scale,eqIntDot,leIntDot]
    omega
  | missing c x =>
    rcases c with ⟨i,t⟩
    rcases x with ⟨j,u,k⟩
    rcases hc with ⟨_,ht,hu,hh⟩
    dsimp at ht hu
    subst t
    subst u
    have hb := missing_partner_bound i j k (by simpa [gUpper,grid] using hh)
    have hbudget := missing_budget i
    simp only [intSlack,intCost,scale,eqIntDot,leIntDot]
    omega
  | pair c e =>
    rcases c with ⟨i,t⟩
    rcases e with ⟨j,u⟩
    rcases hc with ⟨_,htu,hcase⟩
    dsimp at htu hcase
    subst u
    rcases hcase with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · subst t
      have hb := available_internal_partner_bound i j (by simpa [gLower,grid] using hh)
      have hbudget := available_pair_budget i
      simp [intSlack,intCost,scale,eqIntDot,leIntDot,reduceCtorEq]
      omega
    · subst t
      have hb := missing_internal_partner_bound i j (by simpa [gUpper,grid] using hh)
      have hbudget := missing_pair_budget i
      simp [intSlack,intCost,scale,eqIntDot,leIntDot,reduceCtorEq]
      omega
  | z => exact z_slack
  | value => exact value_slack

theorem all_rational_columns (c : Column 152) (hc : columnAllowed data c) :
    0 ≤ slack data dualEq dualLe c := by
  have he : data = reflectedData grid := rfl
  have hi : allowedInt grid c := (allowed_equiv grid c).mp (by simpa only [he] using hc)
  have hh := integer_slack_nonneg grid dualDenominator (by decide) dualEqNumerator dualLeNumerator c
    (all_integer_columns c hi)
  exact hh

theorem dense_rational_columns (c : Column 152) (hc : columnAllowed data c) :
    (∑ r,dualEq r*coeffEq r c)+(∑ r,dualLe r*coeffLe data r c) ≤ cost c :=
  (slack_iff_columns data dualEq dualLe c).mp (all_rational_columns c hc)

end RobustMatching.R7ReductionCertificate.Concrete
#print axioms RobustMatching.R7ReductionCertificate.Concrete.all_rational_columns
