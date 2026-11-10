import RandomOrderMatching.Weights.Truncation.BreakpointMesh

/-! Exact half-open edge membership, including dyadic endpoints. -/
namespace RandomOrderMatching.Weights.Truncation.DyadicMembership
open RandomOrderMatching.Weights.Truncation.DyadicIncrement RandomOrderMatching.Weights.Truncation.PriceMap

theorem window_iff (w : ℝ) (j t : ℤ) (k : ℕ)
    (hj : lo j ≤ w ∧ w < lo (j+1)) :
    (lo t ≤ w ∧ w < up k t) ↔ j-(k:ℤ) < t ∧ t ≤ j := by
  constructor
  · rintro ⟨ht,hk⟩
    have h1 : j < t+(k:ℤ) :=
      (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp (hj.1.trans_lt hk)
    have h2 : t < j+1 :=
      (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp (ht.trans_lt hj.2)
    omega
  · rintro ⟨h1,h2⟩
    exact ⟨(lo_mono h2).trans hj.1, hj.2.trans_le (lo_mono (by omega))⟩

theorem exact_window_filter (T : Finset ℤ) (w : ℝ) (j : ℤ) (k : ℕ)
    (hj : lo j ≤ w ∧ w < lo (j+1)) (hT : Finset.Ioc (j-(k:ℤ)) j ⊆ T) :
    T.filter (fun t => lo t ≤ w ∧ w < up k t) = Finset.Ioc (j-(k:ℤ)) j := by
  classical
  ext t
  simp only [Finset.mem_filter, Finset.mem_Ioc, window_iff w j t k hj]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hT (Finset.mem_Ioc.mpr h),h⟩

theorem exact_k_memberships (T : Finset ℤ) (w : ℝ) (j : ℤ) (k : ℕ)
    (hj : lo j ≤ w ∧ w < lo (j+1)) (hT : Finset.Ioc (j-(k:ℤ)) j ⊆ T) :
    (T.filter (fun t => lo t ≤ w ∧ w < up k t)).card = k := by
  rw [exact_window_filter T w j k hj hT, window_index_count]
end RandomOrderMatching.Weights.Truncation.DyadicMembership
#print axioms RandomOrderMatching.Weights.Truncation.DyadicMembership.window_iff
#print axioms RandomOrderMatching.Weights.Truncation.DyadicMembership.exact_k_memberships
