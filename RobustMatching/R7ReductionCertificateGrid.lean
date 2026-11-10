import RobustMatching.R7ReductionCertificateData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RobustMatching.R7ReductionCertificate.Concrete
theorem data_grid_zero : data.grid 0 = 0 := by decide +kernel
theorem data_grid_last : data.grid ⟨152,by decide⟩ = 1 := by decide +kernel
theorem data_grid_first : data.grid 1 = 1/256 := by decide +kernel
theorem data_grid_strict : ∀ i : Fin 152,data.grid i.castSucc < data.grid i.succ := by decide +kernel
end RobustMatching.R7ReductionCertificate.Concrete
