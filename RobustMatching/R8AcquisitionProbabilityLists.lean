import RobustMatching.R8AcquisitionProbabilityEpochBank

/-! Exact conversion between actual prefix/slice lists and original-label
sets in the permutation model. No random-label or distinct-copy approximation. -/
noncomputable section
namespace RobustMatching.R8AcquisitionProbability
open RobustMatching.R7ProbabilityPermutation RobustMatching.R7ProbabilityStopping
variable {α : Type*} [DecidableEq α]

theorem ofFn_take_toFinset {n : ℕ} (f : Fin n → α) (k : ℕ) :
    ((List.ofFn f).take k).toFinset = (positions k).image f := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hx)
    have hin : i<n := by
      have hh : i < min k n := by simpa using hi
      omega
    have hik : i<k := by
      have hmin : i < min k n := by simpa using hi
      omega
    refine Finset.mem_image.mpr ⟨⟨i,hin⟩,?_,?_⟩
    · simpa [positions] using hik
    · simpa only [List.getElem_take,List.getElem_ofFn] using he
  · intro hx
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hx
    have hik : i.val<k := by simpa [positions] using hi
    apply List.mem_toFinset.mpr
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val,by simp only [List.length_take,List.length_ofFn]; omega,?_⟩
    simpa only [List.getElem_take,List.getElem_ofFn] using he

theorem prefix_list_eq_of_agree {n : ℕ} (f g : Fin n → α) (k : ℕ)
    (h : ∀ i : Fin n,i.val<k → f i=g i) :
    (List.ofFn f).take k = (List.ofFn g).take k := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hin : i<n := by
    have hh : i < min k n := by simpa using hi
    omega
  have hik : i<k := by
    have hh : i < min k n := by simpa using hi
    omega
  simpa only [List.getElem_take,List.getElem_ofFn] using h ⟨i,hin⟩ hik

theorem ofFn_slice_toFinset {n : ℕ} (f : Fin n → α) (k ell : ℕ) :
    (((List.ofFn f).drop k).take ell).toFinset =
      ((positions (k+ell)) \ positions k).image f := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hx)
    have hmin : i < min ell (n-k) := by simpa using hi
    have hn : k+i<n := by omega
    refine Finset.mem_image.mpr ⟨⟨k+i,hn⟩,?_,?_⟩
    · simp only [positions,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
      omega
    · simpa only [List.getElem_take,List.getElem_drop,List.getElem_ofFn] using he
  · intro hx
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hx
    have hi' : i.val<k+ell ∧ ¬i.val<k := by simpa [positions] using hi
    apply List.mem_toFinset.mpr
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val-k,by simp only [List.length_take,List.length_drop,List.length_ofFn]; omega,?_⟩
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    have hk : k+(i.val-k)=i.val := by omega
    simpa only [hk] using he

theorem ofFn_drop_mem_remaining {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (a : Fin n) :
    a ∈ (List.ofFn π).drop k ↔ a ∈ remaining (positions k) π := by
  constructor
  · intro ha
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp ha
    have hin : k+i<n := by
      have hh : i<n-k := by simpa using hi
      omega
    have hva : π ⟨k+i,hin⟩=a := by simpa only [List.getElem_drop,List.getElem_ofFn] using he
    apply mem_remaining.mpr
    intro hs
    obtain ⟨j,hj,hja⟩ := Finset.mem_image.mp hs
    have heq := π.injective (hja.trans hva.symm)
    have hjk : j.val<k := by simpa [positions] using hj
    have hval : j.val=k+i := congrArg Fin.val heq
    omega
  · intro ha
    have hin : (π.symm a).val<n := (π.symm a).isLt
    have hik : k≤(π.symm a).val := by
      by_contra hh
      have hl : (π.symm a).val<k := by omega
      exact mem_remaining.mp ha (Finset.mem_image.mpr
        ⟨π.symm a,by simpa [positions] using hl,π.apply_symm_apply a⟩)
    apply List.mem_iff_getElem.mpr
    refine ⟨(π.symm a).val-k,by simp only [List.length_drop,List.length_ofFn]; omega,?_⟩
    simp only [List.getElem_drop,List.getElem_ofFn]
    have hk : k+((π.symm a).val-k)=(π.symm a).val := by omega
    simpa only [hk] using π.apply_symm_apply a

end RobustMatching.R8AcquisitionProbability
