import RandomOrderMatching.Analysis.Repair.Probability.Clocks
import Mathlib.Data.Finset.Sort

/-! A concrete permutation sorting original-label categorical clocks.
The original index breaks ties, so no independent-copy order is introduced. -/
noncomputable section
set_option maxHeartbeats 800000
open Classical
open scoped BigOperators
namespace RandomOrderMatching.Probability.ClockCoupling
open RandomOrderMatching.Analysis.Repair.Probability

def categoryKey {n : ℕ} (z : Fin n → Clock) (i : Fin n) : ℕ :=
  (z i).val * (n+1) + i.val

lemma categoryKey_injective {n : ℕ} (z : Fin n → Clock) :
    Function.Injective (categoryKey z) := by
  intro i j h
  have he := congrArg (fun a => a % (n+1)) h
  simp only [categoryKey, Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero,
    Nat.zero_mod, zero_add, Nat.mod_eq_of_lt (Nat.lt_succ_of_lt i.isLt),
    Nat.mod_eq_of_lt (Nat.lt_succ_of_lt j.isLt)] at he
  exact Fin.ext he

def categorySort {n : ℕ} (z : Fin n → Clock) : Equiv.Perm (Fin n) := by
  letI : LinearOrder (ULift.{0} (Fin n)) := LinearOrder.lift'
    (fun i : ULift.{0} (Fin n) => categoryKey z i.down) ((categoryKey_injective z).comp ULift.down_injective)
  exact (Fintype.orderIsoFinOfCardEq (ULift.{0} (Fin n))
    (show Fintype.card (ULift.{0} (Fin n)) = n by simp)).toEquiv.trans Equiv.ulift

lemma categoryKey_sort_mono {n : ℕ} (z : Fin n → Clock) :
    Monotone (fun i => categoryKey z (categorySort z i)) := by
  letI : LinearOrder (ULift.{0} (Fin n)) := LinearOrder.lift'
    (fun i : ULift.{0} (Fin n) => categoryKey z i.down) ((categoryKey_injective z).comp ULift.down_injective)
  intro i j hij
  let e := Fintype.orderIsoFinOfCardEq (ULift.{0} (Fin n))
    (show Fintype.card (ULift.{0} (Fin n)) = n by simp)
  exact e.map_rel_iff'.mpr hij

lemma category_of_key_le {n : ℕ} (z : Fin n → Clock) (i j : Fin n)
    (h : categoryKey z i ≤ categoryKey z j) : z i ≤ z j := by
  change (z i).val ≤ (z j).val
  unfold categoryKey at h
  have hi := i.isLt
  have hj := j.isLt
  by_contra hn
  have hz : (z j).val + 1 ≤ (z i).val := by omega
  have hp := Nat.mul_le_mul_right (n+1) hz
  nlinarith

theorem categorySort_monotone {n : ℕ} (z : Fin n → Clock) :
    Monotone (fun i => z (categorySort z i)) := by
  intro i j hij
  exact category_of_key_le z _ _ (categoryKey_sort_mono z hij)

/-- A random relabeling of the positions gives the stream order. -/
def streamOrder {n : ℕ} (z : Fin n → Clock) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) := (categorySort z).trans π

/-- Every original label reads the one clock assigned to its position. -/
def labelClocks {n : ℕ} (z : Fin n → Clock) (π : Equiv.Perm (Fin n)) : Fin n → Clock :=
  fun b => z (π.symm b)

@[simp] lemma labelClocks_streamOrder {n : ℕ} (z : Fin n → Clock)
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    labelClocks z π (streamOrder z π i) = z (categorySort z i) := by
  simp [labelClocks, streamOrder]

theorem coupled_order_monotone {n : ℕ} (z : Fin n → Clock)
    (π : Equiv.Perm (Fin n)) :
    Monotone (fun i => labelClocks z π (streamOrder z π i)) := by
  simpa only [labelClocks_streamOrder] using categorySort_monotone z

end RandomOrderMatching.Probability.ClockCoupling
