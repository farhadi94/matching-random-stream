import Mathlib.Tactic
import Mathlib.Data.Nat.Log

/-! Causal integer geometric cutoff schedule. Index zero denotes the first
cutoff after one original label. No final stream length enters the recurrence. -/
namespace RobustMatching.R8StreamingWrapper
set_option maxHeartbeats 0

def cutoffNext (c : ℕ) : ℕ := (10000001*c+9999999)/10000000

def cutoff : ℕ → ℕ
  | 0 => 1
  | j+1 => cutoffNext (cutoff j)

theorem cutoffNext_lower (c : ℕ) : 10000001*c ≤ 10000000*cutoffNext c := by
  unfold cutoffNext
  omega

theorem cutoffNext_upper (c : ℕ) : 10000000*cutoffNext c < 10000001*c+10000000 := by
  unfold cutoffNext
  omega

theorem cutoffNext_gt {c : ℕ} (hc : 0<c) : c<cutoffNext c := by
  have h := cutoffNext_lower c
  omega

theorem cutoff_pos (j : ℕ) : 0<cutoff j := by
  induction j with
  | zero => decide
  | succ j ih => exact lt_trans ih (cutoffNext_gt ih)

theorem cutoff_strictMono : StrictMono cutoff := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact cutoffNext_gt (cutoff_pos j)

theorem cutoff_index_lower (j : ℕ) : j+1 ≤ cutoff j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h := cutoff_strictMono (Nat.lt_succ_self j)
    simp only [Nat.succ_eq_add_one] at h ⊢
    omega

/-- Exact ceiling semantics for the integer recurrence. -/
theorem cutoffNext_ceil (c : ℕ) :
    cutoffNext c = ⌈(1+(1:ℚ)/10000000)*c⌉₊ := by
  apply le_antisymm
  · by_contra hn
    have hn' : ⌈(1+(1:ℚ)/10000000)*c⌉₊ < cutoffNext c := by omega
    have h := cutoffNext_upper c
    have hh : ⌈(1+(1:ℚ)/10000000)*c⌉₊ *10000000 < 10000001*c := by omega
    have hh' : (⌈(1+(1:ℚ)/10000000)*c⌉₊:ℚ)*10000000 < 10000001*c := by exact_mod_cast hh
    have hceil := Nat.le_ceil ((1+(1:ℚ)/10000000)*c)
    linarith
  · apply Nat.ceil_le.mpr
    have h := cutoffNext_lower c
    have hh : (10000001:ℚ)*c ≤ 10000000*(cutoffNext c:ℚ) := by exact_mod_cast h
    linarith

theorem cutoff_block_growth (n k : ℕ) :
    (10000000+k)*cutoff n ≤ 10000000*cutoff (n+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := cutoff_strictMono.monotone (show n≤n+k by omega)
    have hs := cutoffNext_lower (cutoff (n+k))
    change 10000001*cutoff (n+k) ≤ 10000000*cutoff (n+k+1) at hs
    have he : n+(k+1)=n+k+1 := by omega
    rw [he]
    nlinarith

theorem cutoff_block_doubles (n : ℕ) :
    2*cutoff n ≤ cutoff (n+10000000) := by
  have h := cutoff_block_growth n 10000000
  omega

theorem cutoff_power_lower (k : ℕ) : 2^k ≤ cutoff (10000000*k) := by
  induction k with
  | zero => simp [cutoff]
  | succ k ih =>
    have h := cutoff_block_doubles (10000000*k)
    rw [Nat.mul_add, Nat.mul_one]
    rw [pow_succ]
    omega

def cutoffCountBound (m : ℕ) : ℕ := 10000000*(Nat.log 2 m+1)

theorem cutoff_count_index {j m : ℕ} (hj : cutoff j ≤ m) : j<cutoffCountBound m := by
  have hp := cutoff_power_lower (Nat.log 2 m+1)
  have hm := Nat.lt_pow_succ_log_self (by decide : 1<2) m
  by_contra h
  have hn : cutoffCountBound m ≤ j := by omega
  have hg := cutoff_strictMono.monotone hn
  unfold cutoffCountBound at hg
  omega

def reachedCuts (m : ℕ) : Finset ℕ :=
  ((Finset.range m).image cutoff).filter (fun c => c≤m)

theorem mem_reachedCuts {c m : ℕ} : c∈reachedCuts m ↔ ∃j,cutoff j=c ∧ c≤m := by
  simp only [reachedCuts,Finset.mem_filter,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨⟨j,hj,hc⟩,hm⟩
    exact ⟨j,hc,hm⟩
  · rintro ⟨j,hc,hm⟩
    have h := cutoff_index_lower j
    exact ⟨⟨j,by omega,hc⟩,hm⟩

theorem reachedCuts_mono {a b : ℕ} (hab : a≤b) : reachedCuts a ⊆ reachedCuts b := by
  intro c hc
  obtain ⟨j,hj,hc⟩ := mem_reachedCuts.mp hc
  exact mem_reachedCuts.mpr ⟨j,hj,hc.trans hab⟩

theorem reachedCuts_count (m : ℕ) : (reachedCuts m).card ≤ cutoffCountBound m := by
  have hs : reachedCuts m ⊆ (Finset.range (cutoffCountBound m)).image cutoff := by
    intro c hc
    obtain ⟨j,hj,hc⟩ := mem_reachedCuts.mp hc
    exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (cutoff_count_index (hj ▸ hc)),hj⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans (by simp))

end RobustMatching.R8StreamingWrapper
