import RandomOrderMatching.Streaming.CutoffGrid
namespace RandomOrderMatching.Streaming
set_option maxHeartbeats 0

theorem exists_cutoff_above (t : ℕ) : ∃j,t<cutoff j :=
  ⟨t+1,by have h := cutoff_index_lower (t+1); omega⟩

def firstAbove (t : ℕ) : ℕ := Nat.find (exists_cutoff_above t)
def selectedCutoff (m : ℕ) : ℕ := cutoff (firstAbove (1100001*m/2000000)-1)

theorem firstAbove_spec (t : ℕ) : t<cutoff (firstAbove t) :=
  Nat.find_spec (exists_cutoff_above t)

theorem firstAbove_pos {t : ℕ} (ht : 1≤t) : 0<firstAbove t := by
  have h := firstAbove_spec t
  by_contra hn
  have he : firstAbove t=0 := by omega
  rw [he] at h
  simp [cutoff] at h
  omega

theorem cutoff_before_firstAbove {t : ℕ} (ht : 1≤t) : cutoff (firstAbove t-1)≤t := by
  have hp := firstAbove_pos ht
  have h := Nat.find_min (exists_cutoff_above t) (show firstAbove t-1<firstAbove t by omega)
  omega

theorem selected_cutoff_bounds {m : ℕ} (hm : 10000000≤m) :
    2200001*m ≤ 4000000*selectedCutoff m ∧
    4000000*selectedCutoff m ≤ 2200003*m := by
  let t := 1100001*m/2000000
  have ht : 1≤t := by dsimp [t]; omega
  have hp := firstAbove_pos ht
  have hprev := cutoff_before_firstAbove ht
  have hnext := firstAbove_spec t
  have he : firstAbove t=(firstAbove t-1)+1 := by omega
  rw [he] at hnext
  change t<cutoffNext (cutoff (firstAbove t-1)) at hnext
  have hu := cutoffNext_upper (cutoff (firstAbove t-1))
  change cutoff (firstAbove t-1)≤t at hprev
  change 2200001*m ≤ 4000000*cutoff (firstAbove t-1) ∧
    4000000*cutoff (firstAbove t-1) ≤ 2200003*m
  constructor <;> dsimp [t] at * <;> omega

/-- Current alpha=.55 and omega=.550001 with margin m/(4*10^6). -/
theorem selected_cutoff_clock_bracket {m : ℕ} (hm : 10000000≤m) :
    (11/20:ℝ)*m+(m:ℝ)/4000000 ≤ selectedCutoff m ∧
    (selectedCutoff m:ℝ) ≤ (550001/1000000:ℝ)*m-(m:ℝ)/4000000 := by
  obtain ⟨hl,hu⟩ := selected_cutoff_bounds hm
  have hl' : (2200001:ℝ)*m ≤ 4000000*(selectedCutoff m:ℝ) := by exact_mod_cast hl
  have hu' : 4000000*(selectedCutoff m:ℝ) ≤ (2200003:ℝ)*m := by exact_mod_cast hu
  constructor <;> linarith

theorem selected_cutoff_reached {m : ℕ} (hm : 10000000≤m) :
    selectedCutoff m ∈ reachedCuts m := by
  have hb := (selected_cutoff_bounds hm).2
  exact mem_reachedCuts.mpr ⟨_,rfl,by omega⟩

/-- Restricting any longer bank to the current prefix gives exactly the
causally launched bank. A final-length table cannot introduce future phases. -/
theorem reachedCuts_filter {a b : ℕ} (hab : a≤b) :
    (reachedCuts b).filter (fun c => c≤a) = reachedCuts a := by
  ext c
  simp only [Finset.mem_filter,mem_reachedCuts]
  constructor
  · rintro ⟨⟨j,hj,_⟩,ha⟩
    exact ⟨j,hj,ha⟩
  · rintro ⟨j,hj,ha⟩
    exact ⟨⟨j,hj,ha.trans hab⟩,ha⟩

end RandomOrderMatching.Streaming
