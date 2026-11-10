import RobustMatching.R7ReductionCertificateEnvelopes
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RobustMatching.R7ReductionCertificate.Concrete
open RobustMatching.R7ReductionCertificate

theorem root_budget : ∀ i : Fin 152,∀ k : Fin 4,
    (dualEqNumerator .normalization+dualEqNumerator (.rootEndpoint (i,.S,k))+
      suffixRoot (upperLimit i.val)+dualLeNumerator .mass)*100000000+
      dualLeNumerator .phase*22499950+dualLeNumerator .rootMoment*99999999 ≤ 0 := by decide +kernel
theorem missing_budget : ∀ i : Fin 152,
    (dualEqNumerator (.missingCenter (i,.M))+suffixMissing (upperLimit i.val)+
      dualLeNumerator .mass)*100000000+dualLeNumerator .missingMoment*99999999 ≤ 0 := by decide +kernel
theorem available_pair_budget : ∀ i : Fin 152,
    (dualEqNumerator .internalCount+dualEqNumerator (.internalCenter (i,.I))+
      prefixInternalI (lowerLimit i.val)+dualLeNumerator .mass)*2000000+
      dualLeNumerator .phase*1000000 ≤ 0 := by decide +kernel
theorem missing_pair_budget : ∀ i : Fin 152,
    (dualEqNumerator .internalCount+dualEqNumerator (.internalCenter (i,.J))+
      suffixInternalJ (upperLimit i.val)+dualLeNumerator .mass)*2000000+
      dualLeNumerator .phase*449999 ≤ 0 := by decide +kernel

theorem center_slacks : ∀ c : CenterClass 152,
    0 ≤ intSlack grid dualDenominator dualEqNumerator dualLeNumerator (.center c) := by decide +kernel
theorem outside_slacks : ∀ x : OutsideClass 152,outsideAllowedInt grid x →
    0 ≤ intSlack grid dualDenominator dualEqNumerator dualLeNumerator (.outside x) := by decide +kernel
theorem z_slack : 0 ≤ intSlack grid dualDenominator dualEqNumerator dualLeNumerator .z := by decide +kernel
theorem value_slack : 0 ≤ intSlack grid dualDenominator dualEqNumerator dualLeNumerator .value := by decide +kernel
theorem dual_le_signs : ∀ r : LeRow 152,dualLeNumerator r ≤ 0 := by decide +kernel

end RobustMatching.R7ReductionCertificate.Concrete
#print axioms RobustMatching.R7ReductionCertificate.Concrete.root_budget
#print axioms RobustMatching.R7ReductionCertificate.Concrete.dual_le_signs
