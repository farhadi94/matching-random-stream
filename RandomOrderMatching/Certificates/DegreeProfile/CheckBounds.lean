import RandomOrderMatching.Certificates.DegreeProfile.EnvelopeData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RandomOrderMatching.Certificates.DegreeProfile.Concrete
open RandomOrderMatching.Certificates.DegreeProfile

theorem grid_steps : ∀ i : Fin 152,gridNumerator i.val ≤ gridNumerator (i.val+1) := by decide +kernel
theorem lower_limits : ∀ i : Fin 152,lowerLimit i.val < 152 ∧
    (lowerLimit i.val+1 < 152 → 512 < gridNumerator (lowerLimit i.val+1)+gridNumerator i.val) := by decide +kernel
theorem upper_limits : ∀ i : Fin 152,upperLimit i.val < 152 ∧
    (0 < upperLimit i.val → 100000000*(gridNumerator (upperLimit i.val)+gridNumerator (i.val+1)) < 51199999488) := by decide +kernel
theorem center_majorants : ∀ c : CenterClass 152,
    centerPrice c ≤ centerPrefix c.2 c.1.val ∧ centerPrice c ≤ prefixAll c.1.val := by decide +kernel
theorem center_steps : ∀ t : CenterType,∀ i : Fin 151,
    centerPrefix t i.val ≤ centerPrefix t (i.val+1) := by decide +kernel
theorem all_steps : ∀ i : Fin 151,prefixAll i.val ≤ prefixAll (i.val+1) := by decide +kernel
theorem outside_majorants : ∀ i : Fin 152,∀ k : Fin 4,
    dualEqNumerator (.rootEndpoint (i,.S,k)) ≤ suffixRoot i.val ∧
    dualEqNumerator (.missingOutside (i,.T,k)) ≤ suffixMissing i.val := by decide +kernel
theorem outside_steps : ∀ i : Fin 151,
    suffixRoot (i.val+1) ≤ suffixRoot i.val ∧
    suffixMissing (i.val+1) ≤ suffixMissing i.val := by decide +kernel
theorem internal_majorants : ∀ i : Fin 152,
    dualEqNumerator (.internalCenter (i,.I)) ≤ prefixInternalI i.val ∧
    dualEqNumerator (.internalCenter (i,.J)) ≤ suffixInternalJ i.val := by decide +kernel
theorem internal_steps : ∀ i : Fin 151,
    prefixInternalI i.val ≤ prefixInternalI (i.val+1) ∧
    suffixInternalJ (i.val+1) ≤ suffixInternalJ i.val := by decide +kernel

end RandomOrderMatching.Certificates.DegreeProfile.Concrete
#print axioms RandomOrderMatching.Certificates.DegreeProfile.Concrete.center_majorants
