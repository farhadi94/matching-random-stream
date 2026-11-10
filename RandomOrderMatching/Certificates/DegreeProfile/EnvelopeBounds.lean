import RandomOrderMatching.Certificates.DegreeProfile.CheckBounds
set_option maxHeartbeats 0
namespace RandomOrderMatching.Certificates.DegreeProfile.Concrete
open RandomOrderMatching.Certificates.DegreeProfile

theorem bounded_mono (f : ℕ → ℤ) (N : ℕ)
    (hs : ∀ k,k+1<N → f k ≤ f (k+1)) {i j : ℕ} (hij : i≤j) (hj : j<N) : f i ≤ f j := by
  induction j generalizing i with
  | zero =>
    have hi : i=0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i=j+1
    · subst i; rfl
    · have hi : i≤j := by omega
      exact (ih hi (by omega)).trans (hs j hj)

theorem bounded_anti (f : ℕ → ℤ) (N : ℕ)
    (hs : ∀ k,k+1<N → f (k+1) ≤ f k) {i j : ℕ} (hij : i≤j) (hj : j<N) : f j ≤ f i := by
  have h := bounded_mono (fun k => -f k) N (fun k hk => neg_le_neg (hs k hk)) hij hj
  omega

theorem grid_mono {i j : ℕ} (hij : i≤j) (hj : j<153) : gridNumerator i ≤ gridNumerator j :=
  bounded_mono gridNumerator 153 (fun k hk => grid_steps ⟨k,by omega⟩) hij hj

theorem lower_index (i j : Fin 152)
    (h : gridNumerator i.val+gridNumerator j.val ≤ 512) : j.val ≤ lowerLimit i.val := by
  by_contra hn
  have hj := j.isLt
  have hb := (lower_limits i).2 (by omega)
  have hm := grid_mono (show lowerLimit i.val+1 ≤ j.val by omega) (by omega : j.val<153)
  omega

theorem upper_index (i j : Fin 152)
    (h : 51199999488 ≤ 100000000*(gridNumerator (i.val+1)+gridNumerator (j.val+1))) :
    upperLimit i.val ≤ j.val := by
  by_contra hn
  have hb := (upper_limits i).2 (by omega)
  have hk := (upper_limits i).1
  have hm := grid_mono (show j.val+1 ≤ upperLimit i.val by omega) (by omega : upperLimit i.val<153)
  omega

theorem center_partner_bound (c : CenterClass 152) (i : Fin 152)
    (h : gridNumerator i.val+gridNumerator c.1.val ≤ 512) :
    centerPrice c ≤ centerPrefix c.2 (lowerLimit i.val) := by
  have hm := bounded_mono (centerPrefix c.2) 152
    (fun k hk => center_steps c.2 ⟨k,by omega⟩) (lower_index i c.1 h) (lower_limits i).1
  exact (center_majorants c).1.trans hm

theorem all_partner_bound (c : CenterClass 152) (i : Fin 152)
    (h : gridNumerator i.val+gridNumerator c.1.val ≤ 512) :
    centerPrice c ≤ prefixAll (lowerLimit i.val) := by
  have hm := bounded_mono prefixAll 152 (fun k hk => all_steps ⟨k,by omega⟩)
    (lower_index i c.1 h) (lower_limits i).1
  exact (center_majorants c).2.trans hm

theorem root_partner_bound (i j : Fin 152) (k : Fin 4)
    (h : 51199999488 ≤ 100000000*(gridNumerator (i.val+1)+gridNumerator (j.val+1))) :
    dualEqNumerator (.rootEndpoint (j,.S,k)) ≤ suffixRoot (upperLimit i.val) := by
  have hm := bounded_anti suffixRoot 152 (fun a ha => (outside_steps ⟨a,by omega⟩).1)
    (upper_index i j h) j.isLt
  exact (outside_majorants j k).1.trans hm

theorem missing_partner_bound (i j : Fin 152) (k : Fin 4)
    (h : 51199999488 ≤ 100000000*(gridNumerator (i.val+1)+gridNumerator (j.val+1))) :
    dualEqNumerator (.missingOutside (j,.T,k)) ≤ suffixMissing (upperLimit i.val) := by
  have hm := bounded_anti suffixMissing 152 (fun a ha => (outside_steps ⟨a,by omega⟩).2)
    (upper_index i j h) j.isLt
  exact (outside_majorants j k).2.trans hm

theorem available_internal_partner_bound (i j : Fin 152)
    (h : gridNumerator i.val+gridNumerator j.val ≤ 512) :
    dualEqNumerator (.internalCenter (j,.I)) ≤ prefixInternalI (lowerLimit i.val) := by
  have hm := bounded_mono prefixInternalI 152 (fun a ha => (internal_steps ⟨a,by omega⟩).1)
    (lower_index i j h) (lower_limits i).1
  exact (internal_majorants j).1.trans hm

theorem missing_internal_partner_bound (i j : Fin 152)
    (h : 51199999488 ≤ 100000000*(gridNumerator (i.val+1)+gridNumerator (j.val+1))) :
    dualEqNumerator (.internalCenter (j,.J)) ≤ suffixInternalJ (upperLimit i.val) := by
  have hm := bounded_anti suffixInternalJ 152 (fun a ha => (internal_steps ⟨a,by omega⟩).2)
    (upper_index i j h) j.isLt
  exact (internal_majorants j).2.trans hm

end RandomOrderMatching.Certificates.DegreeProfile.Concrete
