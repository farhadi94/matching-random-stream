import RobustMatching.R8AcquisitionProbabilityCap
import RobustMatching.R7ProbabilityStopping

/-! Finite union over the deterministic acquisition epoch positions. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8AcquisitionProbability
open RobustMatching.R7ProbabilityPermutation RobustMatching.R7ProbabilityStopping

def epochPositions {n : ℕ} (ell j : ℕ) : Finset (Fin n) :=
  positions ((j+1)*ell) \ positions (j*ell)

theorem epochPositions_disjoint {n : ℕ} (ell j : ℕ) :
    Disjoint (epochPositions (n:=n) ell j) (positions (j*ell)) := Finset.sdiff_disjoint

theorem positions_mono {n : ℕ} {a b : ℕ} (hab : a ≤ b) :
    positions (n:=n) a ⊆ positions b := by
  intro i hi
  simp only [positions,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  omega

theorem positions_card {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    (positions (n:=n) k).card = k := by
  simp only [positions,Fin.card_filter_val_lt,Nat.min_eq_right hk]

theorem epochPositions_card {n : ℕ} (ell j : ℕ) (h : (j+1)*ell ≤ n) :
    (epochPositions (n:=n) ell j).card = ell := by
  have hj : j*ell ≤ (j+1)*ell := Nat.mul_le_mul_right ell (Nat.le_succ j)
  have hh := Finset.card_sdiff_add_card_eq_card (positions_mono (n:=n) hj)
  rw [positions_card h,positions_card (hj.trans h)] at hh
  change (epochPositions ell j).card+j*ell=(j+1)*ell at hh
  nlinarith

def badEpochUnion {n : ℕ} (ell Q Γ : ℕ)
    (T : ℕ → Equiv.Perm (Fin n) → Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  (Finset.range Q).biUnion (fun j =>
    badEmptyEpoch (positions (j*ell)) (epochPositions ell j) (T j) Γ)

theorem bad_epoch_union_bound {n : ℕ} (ell Q Γ : ℕ) (hell : 0 < ell)
    (hfit : Q*ell ≤ n)
    (T : ℕ → Equiv.Perm (Fin n) → Finset (Fin n))
    (hT : ∀ j < Q, ∀ π, T j π ⊆ remaining (positions (j*ell)) π)
    (hcausal : ∀ j < Q, ∀ σ π,
      π ∈ cylinder (positions (j*ell)) σ → T j π = T j σ) :
    ((badEpochUnion ell Q Γ T).card : ℝ)/Fintype.card (Equiv.Perm (Fin n)) ≤
      Q * Real.exp (-(ell : ℝ)*Γ/n) := by
  have hlocal (j : ℕ) (hj : j ∈ Finset.range Q) :
      ((badEmptyEpoch (positions (j*ell)) (epochPositions ell j) (T j) Γ).card : ℝ)/
        Fintype.card (Equiv.Perm (Fin n)) ≤ Real.exp (-(ell : ℝ)*Γ/n) := by
    have hjQ := Finset.mem_range.mp hj
    have hc := epochPositions_card ell j ((Nat.mul_le_mul_right ell (Nat.succ_le_of_lt hjQ)).trans hfit)
    have hh := adaptive_empty_epoch_bound (positions (j*ell)) (epochPositions (n:=n) ell j)
      (epochPositions_disjoint ell j) (Finset.card_pos.mp (by omega)) (T j) Γ
      (hT j hjQ) (hcausal j hjQ)
    simpa only [hc,Fintype.card_fin] using hh
  have hc : ((badEpochUnion ell Q Γ T).card : ℝ) ≤
      ∑ j ∈ Finset.range Q,
        ((badEmptyEpoch (positions (j*ell)) (epochPositions (n:=n) ell j) (T j) Γ).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  calc
    _ ≤ (∑ j ∈ Finset.range Q,
        ((badEmptyEpoch (positions (j*ell)) (epochPositions (n:=n) ell j) (T j) Γ).card : ℝ)) /
          Fintype.card (Equiv.Perm (Fin n)) := div_le_div_of_nonneg_right hc (by positivity)
    _ = ∑ j ∈ Finset.range Q,
        ((badEmptyEpoch (positions (j*ell)) (epochPositions (n:=n) ell j) (T j) Γ).card : ℝ) /
          Fintype.card (Equiv.Perm (Fin n)) := Finset.sum_div _ _ _
    _ ≤ ∑ _j ∈ Finset.range Q, Real.exp (-(ell : ℝ)*Γ/n) := Finset.sum_le_sum hlocal
    _ = _ := by simp

theorem copied_records_le_parent_budget {E C : Type*} [DecidableEq E] [DecidableEq C]
    (U : Finset C) (T : Finset E) (batch : E → Finset C) (κ : ℕ)
    (hU : U ⊆ T.biUnion batch) (hb : ∀ e ∈ T, (batch e).card ≤ κ) :
    U.card ≤ κ*T.card := by
  calc
    _ ≤ (T.biUnion batch).card := Finset.card_le_card hU
    _ ≤ ∑ e ∈ T,(batch e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ T,κ := Finset.sum_le_sum hb
    _ = _ := by simp [Nat.mul_comm]

theorem copied_overflow_forces_many_parents {E C : Type*} [DecidableEq E] [DecidableEq C]
    (U : Finset C) (T : Finset E) (batch : E → Finset C) (κ Γ : ℕ)
    (hU : U ⊆ T.biUnion batch) (hb : ∀ e ∈ T, (batch e).card ≤ κ)
    (hover : κ*Γ < U.card) : Γ < T.card := by
  have hh := copied_records_le_parent_budget U T batch κ hU hb
  by_contra hn
  have ht : T.card ≤ Γ := Nat.le_of_not_gt hn
  have hm := Nat.mul_le_mul_left κ ht
  omega

end RobustMatching.R8AcquisitionProbability
