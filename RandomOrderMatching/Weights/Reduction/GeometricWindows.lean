import RandomOrderMatching.Weights.Reduction.Shifts

/-! Exact geometric window membership and residue separation, including
weights exactly on geometric boundaries. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Weights.Reduction.GeometricWindows

theorem exponent_exists {B w : ℝ} (hB : 1 < B) (hw : 0 < w) :
    ∃ j : ℤ,B^j ≤ w ∧ w < B^(j+1) := exists_mem_Ico_zpow hw hB

theorem membership_iff {B w : ℝ} (hB : 1 < B) (j t : ℤ) (k : ℕ)
    (hj : B^j ≤ w ∧ w < B^(j+1)) :
    (B^t ≤ w ∧ w < B^(t+(k:ℤ))) ↔ j-(k:ℤ) < t ∧ t ≤ j := by
  constructor
  · rintro ⟨ht,hk⟩
    have h1 : j < t+(k:ℤ) := (zpow_lt_zpow_iff_right₀ hB).mp (hj.1.trans_lt hk)
    have h2 : t < j+1 := (zpow_lt_zpow_iff_right₀ hB).mp (ht.trans_lt hj.2)
    omega
  · rintro ⟨h1,h2⟩
    exact ⟨(zpow_le_zpow_right₀ hB.le h2).trans hj.1,
      hj.2.trans_le (zpow_le_zpow_right₀ hB.le (by omega))⟩

theorem exact_k_windows {B w : ℝ} (hB : 1 < B) (j : ℤ) (k : ℕ)
    (hj : B^j ≤ w ∧ w < B^(j+1)) :
    {t ∈ Finset.Ioc (j-(k:ℤ)) j | B^t ≤ w ∧ w < B^(t+(k:ℤ))}.card = k := by
  have heq : {t ∈ Finset.Ioc (j-(k:ℤ)) j | B^t ≤ w ∧ w < B^(t+(k:ℤ))} =
      Finset.Ioc (j-(k:ℤ)) j := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_Ioc,membership_iff hB j t k hj,and_self]
  rw [heq]
  simp

/-- Congruent starts of distinct windows are separated by a whole residue period. -/
theorem residue_gap {a b q : ℤ} (hq : 0 < q) (hab : a < b)
    (hmod : a % q = b % q) : a+q ≤ b := by
  have hd : q ∣ b-a := (Int.modEq_iff_dvd).mp hmod
  have hp : 0 < b-a := by omega
  have hle : q ≤ b-a := Int.le_of_dvd hp hd
  omega

/-- Each original edge belongs to at most one window of a fixed residue. -/
theorem unique_start_in_residue {j a b : ℤ} {k : ℕ}
    (ha : j-(k:ℤ) < a ∧ a ≤ j) (hb : j-(k:ℤ) < b ∧ b ≤ j)
    (hmod : a % ((k:ℤ)+1) = b % ((k:ℤ)+1)) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · have hh := residue_gap (by omega : 0 < (k:ℤ)+1) h hmod
    omega
  · exact h
  · have hh := residue_gap (by omega : 0 < (k:ℤ)+1) h hmod.symm
    omega

theorem kept_residue_count (j : ℤ) (k : ℕ) :
    ((Finset.Ioc (j-(k:ℤ)) j).image (fun t => t % ((k:ℤ)+1))).card = k := by
  rw [Finset.card_image_iff.mpr ?_]
  · simp
  · intro a ha b hb heq
    exact unique_start_in_residue (Finset.mem_Ioc.mp ha) (Finset.mem_Ioc.mp hb) heq

def residue (k : ℕ) (t : ℤ) : Fin (k+1) :=
  ⟨(t % ((k:ℤ)+1)).toNat,by
    have h0 := Int.emod_nonneg t (show (k:ℤ)+1 ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos t (show 0 < (k:ℤ)+1 by omega)
    omega⟩

theorem residue_int (k : ℕ) (t : ℤ) : ((residue k t).val:ℤ) = t % ((k:ℤ)+1) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg t (show (k:ℤ)+1 ≠ 0 by omega))

/-- The actual consecutive window starts omit exactly one shift. -/
theorem exists_unique_omitted_shift (j : ℤ) (k : ℕ) :
    ∃ d : Fin (k+1),∀ s : Fin (k+1),
      (∃ t ∈ Finset.Ioc (j-(k:ℤ)) j,residue k t = s) ↔ s ≠ d := by
  classical
  let R := (Finset.Ioc (j-(k:ℤ)) j).image (residue k)
  have hcard : R.card = k := by
    rw [Finset.card_image_iff.mpr ?_]
    · simp
    · intro a ha b hb heq
      have hv := congrArg (fun x : Fin (k+1) => (x.val:ℤ)) heq
      rw [residue_int,residue_int] at hv
      exact unique_start_in_residue (Finset.mem_Ioc.mp ha) (Finset.mem_Ioc.mp hb) hv
  have hmissing : ((Finset.univ : Finset (Fin (k+1))) \ R).card = 1 := by
    rw [Finset.card_sdiff]
    simp [hcard]
  obtain ⟨d,hd⟩ := Finset.card_eq_one.mp hmissing
  refine ⟨d,fun s => ?_⟩
  have hn : s ∉ R ↔ s = d := by
    have hh : s ∈ (Finset.univ : Finset (Fin (k+1))) \ R ↔ s ∈ ({d}:Finset (Fin (k+1))) := by
      rw [hd]
    simpa using hh
  have hy : s ∈ R ↔ s ≠ d := by simpa using not_congr hn
  simpa only [R,Finset.mem_image] using hy

/-- The consecutive starts in one residue instantiate the geometric scale
used by `separated_combine`; no asymptotic approximation is involved. -/
theorem residue_lower_scale {B : ℝ} (hB : B ≠ 0) (t : ℤ) (k i : ℕ) :
    B^(t-((k+1:ℕ):ℤ)*(i:ℤ)) = B^t*(B^(-((k+1:ℕ):ℤ)))^i := by
  have he : t-((k+1:ℕ):ℤ)*(i:ℤ) = t+(-((k+1:ℕ):ℤ))*(i:ℤ) := by ring
  rw [he,zpow_add₀ hB,zpow_mul,zpow_natCast]

theorem residue_upper_scale {B : ℝ} (hB : B ≠ 0) (t : ℤ) (k i : ℕ) :
    B^(t-((k+1:ℕ):ℤ)*(i:ℤ)+(k:ℤ)) =
      (B^t*(B^(-((k+1:ℕ):ℤ)))^i)/(B*B^(-((k+1:ℕ):ℤ))) := by
  rw [zpow_add₀ hB,residue_lower_scale hB,zpow_natCast]
  simp only [zpow_neg,zpow_natCast,pow_succ]
  field_simp

end RandomOrderMatching.Weights.Reduction.GeometricWindows

#print axioms RandomOrderMatching.Weights.Reduction.GeometricWindows.exact_k_windows
#print axioms RandomOrderMatching.Weights.Reduction.GeometricWindows.kept_residue_count
