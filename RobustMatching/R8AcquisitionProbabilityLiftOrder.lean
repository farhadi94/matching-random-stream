import RobustMatching.R8AcquisitionProbabilitySuffix
import RobustMatching.R8AcquisitionProbabilityLists
import RobustMatching.R8PermutationClockFiniteLaw

/-! A concrete enumeration of the remaining original labels by physical
suffix positions, and its exact compatibility with the suffix-law bijection. -/
noncomputable section
open Classical
open scoped BigOperators
namespace RobustMatching.R8AcquisitionProbability
open RobustMatching.R7ProbabilityStopping RobustMatching.R7ProbabilityPermutation

theorem remaining_iff_inverse_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (a : Fin n) :
    a∈remaining (positions k) σ ↔ k≤(σ.symm a).val := by
  rw [mem_remaining]
  constructor
  · intro ha
    by_contra hn
    have hi : σ.symm a∈positions k := by simp only [positions,Finset.mem_filter,Finset.mem_univ,true_and]; omega
    have hm := Finset.mem_image_of_mem σ hi
    exact ha (by simpa only [σ.apply_symm_apply] using hm)
  · intro hk ha
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ha
    have hil : i.val<k := by simpa only [positions,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    have hid : σ.symm a=i := by rw [←he,σ.symm_apply_apply]
    rw [hid] at hk
    omega

def suffixEnumeration {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k≤n) :
    Fin (n-k) ≃ remaining (positions k) σ where
  toFun i := ⟨σ ⟨k+i.val,by have := i.isLt; omega⟩,by
    apply (remaining_iff_inverse_ge σ k _).mpr
    simp only [σ.symm_apply_apply]
    omega⟩
  invFun a := ⟨(σ.symm a.val).val-k,by
    have ha := (remaining_iff_inverse_ge σ k a.val).mp a.property
    have hb := (σ.symm a.val).isLt
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp only [σ.symm_apply_apply]
    omega
  right_inv a := by
    apply Subtype.ext
    have ha := (remaining_iff_inverse_ge σ k a.val).mp a.property
    change σ ⟨k+((σ.symm a.val).val-k),_⟩=a.val
    have he : (⟨k+((σ.symm a.val).val-k),by have := (σ.symm a.val).isLt; omega⟩ : Fin n)=σ.symm a.val := by
      apply Fin.ext
      change k+((σ.symm a.val).val-k)=(σ.symm a.val).val
      omega
    rw [he,σ.apply_symm_apply]

theorem extended_suffix_list {n : ℕ} {E : Type*} (label : Fin n→E)
    (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k≤n)
    (ν : Equiv.Perm (remaining (positions k) σ)) :
    ((List.ofFn (extendSuffix (positions k) σ ν).val).drop k).map label=
      List.ofFn (fun i => label ((ν (suffixEnumeration σ k hk i)).val)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hin : i<n-k := by simpa only [List.length_map,List.length_drop,List.length_ofFn] using hi
  simp only [List.getElem_map,List.getElem_drop,List.getElem_ofFn]
  apply congrArg label
  exact extendSuffix_apply_remaining (positions k) σ ν
    ⟨k+i,by omega⟩ (suffixEnumeration σ k hk ⟨i,hin⟩).property

theorem extended_suffix_reindexed {n : ℕ} {E : Type*} (label : Fin n→E)
    (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k≤n)
    (ν : Equiv.Perm (Fin (n-k))) :
    ((List.ofFn (extendSuffix (positions k) σ ((suffixEnumeration σ k hk).permCongr ν)).val).drop k).map label=
      List.ofFn (fun i => label ((suffixEnumeration σ k hk (ν i)).val)) := by
  rw [extended_suffix_list label σ k hk]
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]

/-- The residual-permutation mean can be evaluated using a uniform permutation
of physical suffix positions, with the exact label enumeration above. -/
theorem residual_event_reindex {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k≤n)
    (P : Equiv.Perm (remaining (positions k) σ) → Prop) :
    ((Finset.univ.filter P).card : ℝ)/Fintype.card (Equiv.Perm (remaining (positions k) σ))=
      (RobustMatching.R8PermutationClock.uniformOrder (n-k)).real
        {ν | P ((suffixEnumeration σ k hk).permCongr ν)} := by
  rw [RobustMatching.R8PermutationClock.uniformOrder_real]
  simp only [Set.mem_setOf_eq]
  have he := (suffixEnumeration σ k hk).permCongr.sum_comp
    (fun ν => if P ν then (1:ℝ) else 0)
  simp only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one] at he
  have hc := Fintype.card_congr (suffixEnumeration σ k hk).permCongr
  rw [he,hc]

end RobustMatching.R8AcquisitionProbability
