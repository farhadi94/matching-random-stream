import RobustMatching.R1OfflinePotential
import RobustMatching.R7GraphKonig
import RobustMatching.R7WeightedPhaseAssemblyRelabel

/-! Actual copied-graph incidence degrees and acquisition potential. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical
namespace RobustMatching.R8Acquisition
open RobustMatching.R2Cut
variable {V : Type*} [Fintype V] [DecidableEq V]

def degree (H : Graph V) (v : V) : ℕ := (H.filter (fun e => v ∈ e.val)).card

def edgeDegree (H : Graph V) (e : Edge V) : ℕ := ∑ v ∈ e.val, degree H v

def Upper (beta : ℕ) (H : Graph V) : Prop := ∀ e ∈ H, edgeDegree H e ≤ beta

def potential (beta : ℕ) (H : Graph V) : ℤ :=
  (2*(beta : ℤ)-1)*(H.card : ℤ)-∑ v, (degree H v : ℤ)^2

theorem degree_empty (v : V) : degree (∅ : Graph V) v = 0 := by simp [degree]

theorem degree_mono {H K : Graph V} (h : H ⊆ K) (v : V) : degree H v ≤ degree K v := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩

theorem edgeDegree_mono {H K : Graph V} (h : H ⊆ K) (e : Edge V) :
    edgeDegree H e ≤ edgeDegree K e :=
  Finset.sum_le_sum (fun v _ => degree_mono h v)

theorem degree_insert {H : Graph V} (e : Edge V) (he : e ∉ H) (v : V) :
    degree (insert e H) v = degree H v + if v ∈ e.val then 1 else 0 := by
  unfold degree
  rw [Finset.filter_insert]
  by_cases hv : v ∈ e.val
  · simp only [hv,if_true]
    exact Finset.card_insert_of_notMem (fun hh => he (Finset.mem_filter.mp hh).1)
  · simp [hv]

theorem degree_erase_int {H : Graph V} (e : Edge V) (he : e ∈ H) (v : V) :
    (degree (H.erase e) v : ℤ) = (degree H v : ℤ) - if v ∈ e.val then 1 else 0 := by
  have hh := degree_insert e (Finset.notMem_erase e H) v
  rw [Finset.insert_erase he] at hh
  have hz : (degree H v : ℤ) = (degree (H.erase e) v : ℤ) +
      if v ∈ e.val then 1 else 0 := by exact_mod_cast hh
  linarith

theorem degree_sum (H : Graph V) : ∑ v, degree H v = 2*H.card := by
  simp only [degree,Finset.card_filter]
  rw [Finset.sum_comm]
  have hh (e : Edge V) : (∑ v : V, if v ∈ e.val then 1 else 0) = 2 := by
    simpa using e.property
  simp_rw [hh]
  simp [mul_comm]

theorem degree_sum_int (H : Graph V) : ∑ v, (degree H v : ℤ) = 2*(H.card : ℤ) := by
  exact_mod_cast degree_sum H

theorem squares_eq_edgeDegrees (H : Graph V) :
    (∑ v, degree H v ^ 2) = ∑ e ∈ H, edgeDegree H e := by
  have hv (v : V) : degree H v ^ 2 = ∑ e ∈ H, if v ∈ e.val then degree H v else 0 := by
    have hh : (∑ e ∈ H, if v ∈ e.val then 1 else 0) = degree H v :=
      (Finset.card_filter (fun e : Edge V => v ∈ e.val) H).symm
    calc
      _ = degree H v * (∑ e ∈ H, if v ∈ e.val then 1 else 0) := by rw [hh,pow_two]
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e he; split_ifs <;> simp
  simp_rw [hv]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp [edgeDegree]

theorem potential_empty (beta : ℕ) : potential beta (∅ : Graph V) = 0 := by
  simp [potential,degree]

theorem potential_upper (beta : ℕ) (H : Graph V) :
    potential beta H ≤ (Fintype.card V : ℤ)*(beta : ℤ)^2 := by
  have hh := R1OfflinePotential.potential_upper (beta : ℤ) (H.card : ℤ)
    (fun v => (degree H v : ℤ)) (degree_sum_int H)
  change 16*potential beta H ≤ _ at hh
  have hn : 0 ≤ (Fintype.card V : ℤ) := Nat.cast_nonneg _
  have hb : 0 ≤ (beta : ℤ) := Nat.cast_nonneg _
  by_cases hz : beta=0
  · subst beta
    unfold potential
    have hs := Finset.sum_nonneg (fun v (_ : v ∈ (Finset.univ : Finset V)) =>
      sq_nonneg (degree H v : ℤ))
    simp only [Nat.cast_zero,mul_zero,zero_sub,neg_mul,one_mul,zero_pow (by decide : 2≠0),mul_zero]
    linarith [Nat.cast_nonneg H.card (α := ℤ)]
  · have hb1 : 1 ≤ (beta : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hs : (2*(beta : ℤ)-1)^2 ≤ 16*(beta : ℤ)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hn
    nlinarith

theorem potential_nonneg {beta : ℕ} (hb : 1 ≤ beta) {H : Graph V} (hH : Upper beta H) :
    0 ≤ potential beta H := by
  have hs : (∑ v, degree H v ^ 2) ≤ H.card*beta := by
    rw [squares_eq_edgeDegrees]
    exact (Finset.sum_le_sum hH).trans_eq (by simp)
  have hz : (∑ v, (degree H v : ℤ)^2) ≤ (H.card : ℤ)*(beta : ℤ) := by exact_mod_cast hs
  have hb1 : 1 ≤ (beta : ℤ) := by exact_mod_cast hb
  unfold potential
  nlinarith [Nat.cast_nonneg H.card (α := ℤ)]

end RobustMatching.R8Acquisition
