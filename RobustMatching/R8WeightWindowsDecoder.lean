import RobustMatching.R8WeightWindowsGrid
import RobustMatching.R7ReductionCompiler

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RobustMatching.R8WeightWindows
open RobustMatching.R2Cut RobustMatching.R7ReductionWindows
open RobustMatching.R7ReductionGreedy RobustMatching.R7ReductionShifts
variable {V : Type*} [DecidableEq V]

def topStart (T : Finset ℤ) : ℤ := (insert 0 T).max' (by simp)
def bottomStart (T : Finset ℤ) : ℤ := (insert 0 T).min' (by simp)
def levelCount (T : Finset ℤ) : ℕ := (topStart T-bottomStart T).toNat+1
theorem mem_start_bounds (T : Finset ℤ) {t : ℤ} (ht : t ∈ T) :
    bottomStart T ≤ t ∧ t ≤ topStart T :=
  ⟨Finset.min'_le _ _ (Finset.mem_insert_of_mem ht),
    Finset.le_max' _ _ (Finset.mem_insert_of_mem ht)⟩

namespace Parameters
variable (p : Parameters) (w : Edge V → ℚ)

def omitted (e : Edge V) : Fin (p.k+1) :=
  Classical.choose (exists_unique_omitted_shift (p.exponent (w e)) p.k)

theorem omitted_iff (hw : ∀ e,0 < w e) (e : Edge V) (s : Fin (p.k+1)) :
    s ≠ p.omitted w e ↔ ∃ t ∈ p.windows (w e), residue p.k t = s := by
  have hh := (Classical.choose_spec
    (exists_unique_omitted_shift (p.exponent (w e)) p.k)) s
  simpa only [omitted, windows, if_pos (hw e)] using hh.symm

theorem lastStart_of_window (hw : ∀ e,0 < w e) (e : Edge V)
    (s : Fin (p.k+1)) (t : ℤ) (ht : t ∈ p.windows (w e))
    (hs : residue p.k t = s) : lastStart p.k s (p.exponent (w e)) = t := by
  have hi : p.exponent (w e)-(p.k:ℤ) < t ∧ t ≤ p.exponent (w e) := by
    simpa only [windows, if_pos (hw e), Finset.mem_Ioc] using ht
  exact lastStart_unique _ _ _ _ (by omega) hs

theorem chosen_window (hw : ∀ e,0 < w e) (e : Edge V) (s : Fin (p.k+1))
    (hs : s ≠ p.omitted w e) :
    lastStart p.k s (p.exponent (w e)) ∈ p.windows (w e) := by
  obtain ⟨t,ht,hr⟩ := (p.omitted_iff w hw e s).mp hs
  rw [p.lastStart_of_window w hw e s t ht hr]
  exact ht

def levelStart (T : Finset ℤ) (s : Fin (p.k+1)) (i : ℕ) : ℤ :=
  gridStart p.k s (topStart T) i
def levelIndex (T : Finset ℤ) (s : Fin (p.k+1)) (e : Edge V) : ℕ :=
  gridIndex p.k s (topStart T) (lastStart p.k s (p.exponent (w e)))
def levels (T : Finset ℤ) (out : ℤ → Graph V) (s : Fin (p.k+1)) (i : ℕ) : Graph V :=
  if p.levelStart T s i ∈ T then out (p.levelStart T s i) else ∅
def residueAnswer (T : Finset ℤ) (out : ℤ → Graph V) (s : Fin (p.k+1)) : Graph V :=
  combine (p.levels T out s) (levelCount T)

theorem index_of_level (hw : ∀ e,0 < w e) (T : Finset ℤ) (out : ℤ → Graph V)
    (hout : ∀ t ∈ T,∀ e ∈ out t,p.contains t (w e))
    (s : Fin (p.k+1)) (i : ℕ) (e : Edge V) (he : e ∈ p.levels T out s i) :
    p.levelIndex w T s e = i := by
  unfold levels at he
  split_ifs at he with ht
  · have hmem := (p.mem_windows (hw e) _).mpr (hout _ ht e he)
    have hs := gridStart_residue p.k s (topStart T) i
    have hh := p.lastStart_of_window w hw e s _ hmem hs
    unfold levelIndex
    rw [hh]
    exact gridIndex_gridStart _ _ _ _
  · simp at he

theorem source_index (hw : ∀ e,0 < w e) (M : Graph V) (T : Finset ℤ)
    (hcover : ∀ e ∈ M,p.windows (w e) ⊆ T)
    (s : Fin (p.k+1)) (e : Edge V) (he : e ∈ kept M (p.omitted w) s) :
    p.levelIndex w T s e < levelCount T ∧
    p.levelStart T s (p.levelIndex w T s e) = lastStart p.k s (p.exponent (w e)) := by
  obtain ⟨heM,hed⟩ := Finset.mem_filter.mp he
  have hwj := p.chosen_window w hw e s (Ne.symm hed)
  have hT := hcover e heM hwj
  have hb := mem_start_bounds T hT
  exact ⟨gridIndex_bound _ _ hb.2 hb.1,
    gridStart_gridIndex _ _ hb.2 (lastStart_residue _ _ _)⟩

theorem residue_approximation (hw : ∀ e,0 < w e) (M : Graph V) (T : Finset ℤ)
    (out : ℤ → Graph V) {alpha : ℝ} (ha : 0 ≤ alpha)
    (hcover : ∀ e ∈ M,p.windows (w e) ⊆ T)
    (hmatch : ∀ t ∈ T,Matching (out t))
    (hout : ∀ t ∈ T,∀ e ∈ out t,p.contains t (w e))
    (hlocal : ∀ t ∈ T,alpha*(∑ e ∈ M.filter (fun e => p.contains t (w e)),(w e:ℝ)) ≤
      ∑ e ∈ out t,(w e:ℝ)) :
    ∃ s : Fin (p.k+1), Matching (p.residueAnswer T out s) ∧
      (alpha*((p.k:ℝ)/(p.k+1))/(1+2/((p.B:ℝ)*(1-(p.B:ℝ)^(-((p.k+1:ℕ):ℤ))))))*
        (∑ e ∈ M,(w e:ℝ)) ≤ ∑ e ∈ p.residueAnswer T out s,(w e:ℝ) := by
  have hB0 : 0 < (p.B:ℝ) := lt_trans zero_lt_one p.base_real
  have hr : 0 < (p.B:ℝ)^(-((p.k+1:ℕ):ℤ)) := zpow_pos hB0 _
  have hr1 : (p.B:ℝ)^(-((p.k+1:ℕ):ℤ)) < 1 := by
    rw [← zpow_zero (p.B:ℝ)]
    exact (zpow_lt_zpow_iff_right₀ p.base_real).mpr (by omega)
  have hlevels (s : Fin (p.k+1)) (i : ℕ) : Matching (p.levels T out s i) := by
    unfold levels
    split_ifs with ht
    · exact hmatch _ ht
    · simp [Matching]
  have h := RobustMatching.R7ReductionCompiler.shifted_compiler M (fun e => (w e:ℝ))
    (Nat.succ_pos p.k) (p.omitted w) (p.levels T out) (fun _ => levelCount T)
    (p.levelIndex w T) (fun s => (p.B:ℝ)^(lastStart p.k s (topStart T)))
    ha hr hr1 hB0 (fun s => (zpow_pos hB0 _).le)
    (fun s i _ e he => p.index_of_level w hw T out hout s i e he)
    (fun s e he => (p.source_index w hw M T hcover s e he).1)
    hlevels ?_ ?_
  · simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, add_sub_cancel_right, residueAnswer] using h
  · intro s i hi e he
    unfold levels at he
    split_ifs at he with ht
    · have hh := hout _ ht e he
      have hrw : (p.B:ℝ)^(p.levelStart T s i) ≤ (w e:ℝ) ∧
          (w e:ℝ) < (p.B:ℝ)^(p.levelStart T s i+(p.k:ℤ)) := by
        exact_mod_cast hh
      have hp : (p.B:ℝ)^(p.levelStart T s i) ≤ (w e:ℝ) ∧
          (w e:ℝ) ≤ (p.B:ℝ)^(p.levelStart T s i+(p.k:ℤ)) := ⟨hrw.1,hrw.2.le⟩
      simpa only [levelStart, gridStart,
        show (p.k:ℤ)+1 = ((p.k+1:ℕ):ℤ) by simp,
        residue_lower_scale (ne_of_gt hB0), residue_upper_scale (ne_of_gt hB0)]
        using hp
    · simp at he
  · intro s i hi
    let F := (kept M (p.omitted w) s).filter (fun e => p.levelIndex w T s e = i)
    have hsub : F ⊆ M.filter (fun e => p.contains (p.levelStart T s i) (w e)) := by
      intro e he
      obtain ⟨heK,hei⟩ := Finset.mem_filter.mp he
      have hs := (p.source_index w hw M T hcover s e heK).2
      rw [hei] at hs
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp heK).1,?_⟩
      rw [hs]
      exact (p.mem_windows (hw e) _).mp
        (p.chosen_window w hw e s (Ne.symm (Finset.mem_filter.mp heK).2))
    by_cases ht : p.levelStart T s i ∈ T
    · unfold levels
      rw [if_pos ht]
      exact (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => by exact_mod_cast (hw e).le)) ha).trans
        (hlocal _ ht)
    · have hF : F = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        have hh := Finset.mem_filter.mp (hsub he)
        exact ht (hcover e hh.1 ((p.mem_windows (hw e) _).mpr hh.2))
      change alpha*(∑ e ∈ F,(w e:ℝ)) ≤ _
      simp [hF, levels, ht]

end Parameters
end RobustMatching.R8WeightWindows
