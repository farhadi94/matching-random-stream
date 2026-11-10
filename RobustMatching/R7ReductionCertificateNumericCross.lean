import RobustMatching.R7ReductionCertificateEnvelopes
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RobustMatching.R7ReductionCertificate.Concrete
open RobustMatching.R7ReductionCertificate

theorem cross_budget : ∀ t : CenterType,∀ x : OutsideClass 152,
    outsideAllowedInt grid x →
    (centerPrefix t (lowerLimit x.1.val)+outsidePrice x)*(1000000*denominator grid x)+
      dualLeNumerator .phase*(25600*edgeInt (representative t) x) ≤ 0 := by decide +kernel

theorem internal_budget : ∀ c : CenterClass 152,
    centerPrice c+prefixAll (lowerLimit c.1.val)+dualLeNumerator .mass ≤ 0 := by decide +kernel

end RobustMatching.R7ReductionCertificate.Concrete
#print axioms RobustMatching.R7ReductionCertificate.Concrete.cross_budget
