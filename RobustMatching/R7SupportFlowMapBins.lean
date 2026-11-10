import RobustMatching.R7SupportFlowMapActualReference

/-! Every normalized graph degree has an admissible interval in the
concrete adaptive grid, including both endpoints 0 and 1. -/
noncomputable section
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate

theorem concrete_upper_le_one : ∀ i : Fin 152, upper Concrete.data i ≤ 1 := by
  decide +kernel
theorem concrete_lower_nonnegative : ∀ i : Fin 152, 0 ≤ lower Concrete.data i := by
  decide +kernel
theorem concrete_positive_bin : ∀ i : Fin 152, i.val ≠ 0 → 1/256 ≤ lower Concrete.data i := by
  decide +kernel

theorem exists_concrete_bin (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ i : Fin 152, (lower Concrete.data i : ℝ) ≤ a ∧ a ≤ (upper Concrete.data i : ℝ) := by
  classical
  let S := Finset.univ.filter fun i : Fin 152 => a ≤ (upper Concrete.data i : ℝ)
  have hlast : (⟨151,by decide⟩ : Fin 152) ∈ S := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    have h := Concrete.data_grid_last
    change Concrete.data.grid (⟨151,by decide⟩ : Fin 152).succ=1 at h
    simpa only [upper,h,Rat.cast_one] using ha1
  have hs : S.Nonempty := ⟨_,hlast⟩
  let i := S.min' hs
  have hi : i ∈ S := Finset.min'_mem S hs
  refine ⟨i,?_,(Finset.mem_filter.mp hi).2⟩
  by_cases hi0 : i.val=0
  · have hiz : i=0 := Fin.ext hi0
    have hz : lower Concrete.data i=0 := by rw [hiz]; exact Concrete.data_grid_zero
    simpa only [hz,Rat.cast_zero] using ha0
  · by_contra hlo
    have hlt : a < (lower Concrete.data i : ℝ) := lt_of_not_ge hlo
    let j : Fin 152 := ⟨i.val-1,by omega⟩
    have hjnext : j.succ=i.castSucc := by apply Fin.ext; simp [j]; omega
    have hjmem : j ∈ S := by
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
      simpa only [upper,hjnext,lower] using hlt.le
    have hij : i ≤ j := Finset.min'_le S j hjmem
    have hij' : i.val ≤ j.val := hij
    simp only [j] at hij'
    omega

def concreteBin (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : Fin 152 :=
  (exists_concrete_bin a ha0 ha1).choose

theorem concreteBin_bounds (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (lower Concrete.data (concreteBin a ha0 ha1) : ℝ) ≤ a ∧
      a ≤ (upper Concrete.data (concreteBin a ha0 ha1) : ℝ) :=
  (exists_concrete_bin a ha0 ha1).choose_spec

end RobustMatching.R7SupportFlowMap
#print axioms RobustMatching.R7SupportFlowMap.exists_concrete_bin
