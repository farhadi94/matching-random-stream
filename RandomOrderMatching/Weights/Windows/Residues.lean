import RandomOrderMatching.Weights.Windows.Arithmetic

noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Weights.Windows
open RandomOrderMatching.Weights.Reduction.GeometricWindows

/-- Largest integer at most j in the residue class s modulo k+1. -/
def lastStart (k : ℕ) (s : Fin (k+1)) (j : ℤ) : ℤ :=
  j - (j - (s.val:ℤ)) % ((k:ℤ)+1)

theorem lastStart_interval (k : ℕ) (s : Fin (k+1)) (j : ℤ) :
    j-((k:ℤ)+1) < lastStart k s j ∧ lastStart k s j ≤ j := by
  have h0 := Int.emod_nonneg (j-(s.val:ℤ)) (by omega : (k:ℤ)+1 ≠ 0)
  have h1 := Int.emod_lt_of_pos (j-(s.val:ℤ)) (by omega : 0 < (k:ℤ)+1)
  unfold lastStart
  omega

theorem lastStart_mod (k : ℕ) (s : Fin (k+1)) (j : ℤ) :
    lastStart k s j % ((k:ℤ)+1) = (s.val:ℤ) := by
  have hs0 : 0 ≤ (s.val:ℤ) := by omega
  have hs1 : (s.val:ℤ) < (k:ℤ)+1 := by omega
  have hid := Int.emod_add_mul_ediv (j-(s.val:ℤ)) ((k:ℤ)+1)
  have he : lastStart k s j = (s.val:ℤ) + ((k:ℤ)+1)*((j-(s.val:ℤ))/((k:ℤ)+1)) := by
    unfold lastStart
    omega
  rw [he]
  simp [Int.add_emod, Int.emod_eq_of_lt hs0 hs1]

theorem lastStart_residue (k : ℕ) (s : Fin (k+1)) (j : ℤ) :
    residue k (lastStart k s j) = s := by
  apply Fin.ext
  have hh := lastStart_mod k s j
  exact_mod_cast (residue_int k (lastStart k s j)).trans hh

theorem lastStart_unique (k : ℕ) (s : Fin (k+1)) (j t : ℤ)
    (ht : j-((k:ℤ)+1) < t ∧ t ≤ j) (hr : residue k t = s) :
    lastStart k s j = t := by
  have hmod : lastStart k s j % ((k:ℤ)+1) = t % ((k:ℤ)+1) := by
    rw [lastStart_mod, ← residue_int, hr]
  have hi := lastStart_interval k s j
  rcases lt_trichotomy (lastStart k s j) t with h | h | h
  · have hh := residue_gap (by omega : 0 < (k:ℤ)+1) h hmod
    omega
  · exact h
  · have hh := residue_gap (by omega : 0 < (k:ℤ)+1) h hmod.symm
    omega

theorem le_lastStart (k : ℕ) (s : Fin (k+1)) {j t : ℤ}
    (ht : t ≤ j) (hr : residue k t = s) : t ≤ lastStart k s j := by
  by_contra hn
  have hmod : lastStart k s j % ((k:ℤ)+1) = t % ((k:ℤ)+1) := by
    rw [lastStart_mod, ← residue_int, hr]
  have hh := residue_gap (by omega : 0 < (k:ℤ)+1) (by omega) hmod
  have hi := lastStart_interval k s j
  omega

def gridStart (k : ℕ) (s : Fin (k+1)) (top : ℤ) (i : ℕ) : ℤ :=
  lastStart k s top - ((k:ℤ)+1)*(i:ℤ)
def gridIndex (k : ℕ) (s : Fin (k+1)) (top t : ℤ) : ℕ :=
  ((lastStart k s top-t)/((k:ℤ)+1)).toNat

theorem gridStart_residue (k : ℕ) (s : Fin (k+1)) (top : ℤ) (i : ℕ) :
    residue k (gridStart k s top i) = s := by
  apply Fin.ext
  have hh : gridStart k s top i % ((k:ℤ)+1) = (s.val:ℤ) := by
    simp [gridStart, Int.sub_emod, lastStart_mod]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  exact_mod_cast (residue_int k _).trans hh

theorem gridIndex_gridStart (k : ℕ) (s : Fin (k+1)) (top : ℤ) (i : ℕ) :
    gridIndex k s top (gridStart k s top i) = i := by
  unfold gridIndex gridStart
  have hq : (k:ℤ)+1 ≠ 0 := by omega
  simp [hq]

theorem gridStart_gridIndex (k : ℕ) (s : Fin (k+1)) {top t : ℤ}
    (ht : t ≤ top) (hr : residue k t = s) :
    gridStart k s top (gridIndex k s top t) = t := by
  have ht' := le_lastStart k s ht hr
  have hd : 0 ≤ (lastStart k s top-t)/((k:ℤ)+1) :=
    Int.ediv_nonneg (by omega) (by omega)
  have hm : (lastStart k s top-t) % ((k:ℤ)+1) = 0 := by
    rw [Int.sub_emod, lastStart_mod, ← residue_int k t, hr]
    simp
  have hid := Int.emod_add_mul_ediv (lastStart k s top-t) ((k:ℤ)+1)
  unfold gridStart gridIndex
  rw [Int.toNat_of_nonneg hd]
  rw [hm] at hid
  omega

theorem gridIndex_bound (k : ℕ) (s : Fin (k+1)) {top bottom t : ℤ}
    (htop : t ≤ top) (hbottom : bottom ≤ t) :
    gridIndex k s top t < (top-bottom).toNat+1 := by
  have htop' := (lastStart_interval k s top).2
  have hdiv : (lastStart k s top-t)/((k:ℤ)+1) ≤ top-bottom := by
    apply (Int.ediv_le_iff_le_mul (by omega : 0 < (k:ℤ)+1)).mpr
    have hp : 0 ≤ (top-bottom)*(k:ℤ) := mul_nonneg (by omega) (by omega)
    nlinarith
  unfold gridIndex
  have hn := Int.toNat_le_toNat hdiv
  omega

end RandomOrderMatching.Weights.Windows
