import RobustMatching.R8PermutationClockBracket
import Mathlib.Order.Interval.Finset.Fin

/-! The bracket implies the exact containment properties required by the
phase construction: every active original is in the prefix, and every
late original is in the suffix. -/
noncomputable section
open Classical
namespace RobustMatching.R8PermutationClock
open R8RepairProbability

lemma filter_count_perm {n : ℕ} (p : Fin n → Prop) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun i => p (σ i)).card = (Finset.univ.filter p).card := by
  apply Finset.card_bij (fun i _ => σ i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i hi j hj hij
    exact σ.injective hij
  · intro j hj
    refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, σ.apply_symm_apply] using hj

lemma activeCount_perm {n : ℕ} (z : Fin n → Clock) (σ : Equiv.Perm (Fin n)) :
    activeCount (fun i => z (σ i)) = activeCount z := by
  unfold activeCount
  convert filter_count_perm (fun b => z b = 0) σ using 1 <;>
    congr 1 <;> ext i <;> simp

lemma earlyCount_perm {n : ℕ} (z : Fin n → Clock) (σ : Equiv.Perm (Fin n)) :
    earlyCount (fun i => z (σ i)) = earlyCount z := by
  unfold earlyCount
  convert filter_count_perm (fun b => z b ≠ 2) σ using 1 <;>
    congr 1 <;> ext i <;> simp

lemma sorted_active_position {n : ℕ} (z : Fin n → Clock) (hm : Monotone z)
    (i : Fin n) (hz : z i = 0) : i.val < activeCount z := by
  have hs : Finset.Iic i ⊆ Finset.univ.filter (fun j => z j = 0) := by
    intro j hj
    have hji : j ≤ i := Finset.mem_Iic.mp hj
    have hc := hm hji
    rw [hz] at hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm hc (Fin.zero_le _)⟩
  have hc := Finset.card_le_card hs
  rw [Fin.card_Iic] at hc
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hc

lemma sorted_late_position {n : ℕ} (z : Fin n → Clock) (hm : Monotone z)
    (i : Fin n) (hz : z i = 2) : earlyCount z ≤ i.val := by
  have hs : Finset.univ.filter (fun j => z j ≠ 2) ⊆ Finset.Iio i := by
    intro j hj
    have hne := (Finset.mem_filter.mp hj).2
    apply Finset.mem_Iio.mpr
    by_contra hn
    have hc := hm (le_of_not_gt hn)
    rw [hz] at hc
    have htop : z j ≤ (2 : Clock) := by
      have hzj := (z j).isLt
      change (z j).val ≤ 2
      omega
    exact hne (le_antisymm htop hc)
  have hc := Finset.card_le_card hs
  simpa only [Fin.card_Iio, earlyCount] using hc

/-- Every category-zero label precedes the selected cutoff, and every
category-two label occurs at or after it. Positions are zero based. -/
theorem bracket_chronology {n : ℕ} (z : Fin n → Clock) (σ : Equiv.Perm (Fin n))
    (hm : Monotone (fun i => z (σ i))) (c : ℕ) (hc : cutoffBracket c z) :
    (∀ b, z b = 0 → (σ.symm b).val < c) ∧
    (∀ b, z b = 2 → c ≤ (σ.symm b).val) := by
  constructor
  · intro b hb
    have h := sorted_active_position (fun i => z (σ i)) hm (σ.symm b) (by simpa using hb)
    rw [activeCount_perm] at h
    exact lt_of_lt_of_le h hc.1
  · intro b hb
    have h := sorted_late_position (fun i => z (σ i)) hm (σ.symm b) (by simpa using hb)
    rw [earlyCount_perm] at h
    exact hc.2.trans h

theorem coupled_bracket_chronology {n : ℕ}
    (s : (Fin n → Clock) × Equiv.Perm (Fin n)) (c : ℕ)
    (hc : cutoffBracket c (coupledClocks s)) :
    (∀ b, coupledClocks s b = 0 → ((coupledOrder s).symm b).val < c) ∧
    (∀ b, coupledClocks s b = 2 → c ≤ ((coupledOrder s).symm b).val) :=
  bracket_chronology _ _ (coupled_chronology s) c hc

end RobustMatching.R8PermutationClock
