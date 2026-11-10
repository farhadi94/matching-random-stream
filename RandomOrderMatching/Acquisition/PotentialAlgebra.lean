import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace RandomOrderMatching.Acquisition.PotentialAlgebra

/-- Simultaneous degree change at the distinct endpoints of a graph edge. -/
def endpointUpdate {V : Type*} [DecidableEq V]
    (d : V → ℤ) (u v : V) (a : ℤ) (z : V) : ℤ :=
  d z + (if z=u then a else 0) + (if z=v then a else 0)

def potential {V : Type*} [Fintype V] (beta m : ℤ) (d : V → ℤ) : ℤ :=
  (2*beta-1)*m - ∑ z, (d z)^2

/-- Exact sum-of-squares change under an edge insertion/deletion. -/
theorem square_update {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℤ) (u v : V) (huv : u ≠ v) (a : ℤ) :
    (∑ z, endpointUpdate d u v a z ^ 2) - (∑ z, d z ^ 2) =
      2*a*(d u+d v) + 2*a^2 := by
  have hp (z : V) : endpointUpdate d u v a z ^ 2 = d z ^ 2 +
      (if z=u then 2*a*d u+a^2 else 0) + (if z=v then 2*a*d v+a^2 else 0) := by
    by_cases hzu : z=u <;> by_cases hzv : z=v <;>
      simp_all [endpointUpdate] <;> ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp
  ring

/-- Each permitted insertion raises the integer potential by at least one. -/
theorem insertion_increases {V : Type*} [Fintype V] [DecidableEq V]
    (beta m : ℤ) (d : V → ℤ) (u v : V) (huv : u ≠ v)
    (hunder : d u+d v ≤ beta-2) :
    potential beta m d + 1 ≤ potential beta (m+1) (endpointUpdate d u v 1) := by
  have hsq := square_update d u v huv 1
  unfold potential
  nlinarith

/-- Each permitted deletion raises the same potential by at least one. -/
theorem deletion_increases {V : Type*} [Fintype V] [DecidableEq V]
    (beta m : ℤ) (d : V → ℤ) (u v : V) (huv : u ≠ v)
    (hover : beta+1 ≤ d u+d v) :
    potential beta m d + 1 ≤ potential beta (m-1) (endpointUpdate d u v (-1)) := by
  have hsq := square_update d u v huv (-1)
  unfold potential
  nlinarith

/-- The potential upper bound needs only the handshake identity; degree bounds during
intermediate updates are unnecessary. -/
theorem potential_upper {V : Type*} [Fintype V]
    (beta m : ℤ) (d : V → ℤ) (hhandshake : ∑ z, d z = 2*m) :
    16 * potential beta m d ≤ (Fintype.card V : ℤ) * (2*beta-1)^2 := by
  have hs := Finset.sum_nonneg (s := (Finset.univ : Finset V))
    (f := fun z => (4*d z-(2*beta-1))^2) (fun z _ => sq_nonneg _)
  have hp (z : V) : (4*d z-(2*beta-1))^2 =
      16*(d z)^2 - 8*(2*beta-1)*d z + (2*beta-1)^2 := by ring
  simp_rw [hp] at hs
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hhandshake] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  unfold potential
  nlinarith

#print axioms square_update
#print axioms insertion_increases
#print axioms deletion_increases
#print axioms potential_upper
end RandomOrderMatching.Acquisition.PotentialAlgebra
