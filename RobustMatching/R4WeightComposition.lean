import RobustMatching.R4WeightDyadic
import RobustMatching.R4WeightDual

/-! Weighted interval budget from explicit finite breakpoint certificates.
The cost coefficients are arbitrary nonnegative reals: odd-set matching costs
and the two rank costs of matroid intersection are both specializations. -/
open scoped BigOperators
namespace RobustMatching.R4WeightComposition
open RobustMatching.R4WeightTruncation RobustMatching.R4WeightDyadic

structure Mesh (T : Finset ℤ) (k : ℕ) (a b : ℝ) where
  steps : ℕ
  point : ℕ → ℝ
  first : point 0 = a
  last : point steps = b
  mono : ∀ j < steps, point j ≤ point (j+1)
  pieces : ∀ j < steps, ∀ i ∈ T, Piece (lo i) (up k i) (point j) (point (j+1))

theorem interval_budget (T : Finset ℤ) (k : ℕ) (hk : 1 ≤ k) (a b : ℝ)
    (mesh : Mesh T k a b) :
    (∑ i ∈ T, (trunc (lo i) (up k i) b-trunc (lo i) (up k i) a)) ≤
      ((k:ℝ)+5)*(b-a) := by
  simpa only [mesh.first, mesh.last] using
    mesh_increment T k mesh.steps hk mesh.point mesh.mono mesh.pieces

/-- Derives the summed price budget from the truncation functions themselves;
no localization or summed-cost hypothesis is assumed. -/
theorem weighted_interval_budget {C : Type*} [DecidableEq C]
    (S : Finset C) (T : Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (a b cost : C → ℝ) (hcost : ∀ c ∈ S, 0 ≤ cost c)
    (meshes : ∀ c ∈ S, Mesh T k (a c) (b c)) :
    (∑ i ∈ T, ∑ c ∈ S, cost c *
      (trunc (lo i) (up k i) (b c)-trunc (lo i) (up k i) (a c))) ≤
      ((k:ℝ)+5) * ∑ c ∈ S, cost c*(b c-a c) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (interval_budget T k hk (a c) (b c) (meshes c hc)) (hcost c hc)
  nlinarith

/-- Deterministic assembly, independent of how correlated local answers were chosen. -/
theorem assemble {C : Type*} [DecidableEq C]
    (S : Finset C) (T : Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (a b cost : C → ℝ) (hcost : ∀ c ∈ S, 0 ≤ cost c)
    (meshes : ∀ c ∈ S, Mesh T k (a c) (b c))
    (answer : ℤ → ℝ) (alpha source : ℝ)
    (hlower : alpha*(k:ℝ)*source ≤ ∑ i ∈ T, answer i)
    (hupper : ∀ i ∈ T, answer i ≤ ∑ c ∈ S, cost c *
      (trunc (lo i) (up k i) (b c)-trunc (lo i) (up k i) (a c))) :
    alpha*(k:ℝ)/((k:ℝ)+5)*source ≤ ∑ c ∈ S, cost c*(b c-a c) := by
  have hsum := Finset.sum_le_sum hupper
  have hbudget := weighted_interval_budget S T k hk a b cost hcost meshes
  have hpos : 0 < (k:ℝ)+5 := by positivity
  convert (show alpha*(k:ℝ)*source/((k:ℝ)+5) ≤
    (∑ c ∈ S, cost c*(b c-a c)) from (div_le_iff₀ hpos).mpr (by linarith)) using 1 <;> ring

/-- Explicit error allowance: k epsilon >= 15, eta=zeta=epsilon/3. -/
theorem accuracy_budget (alpha eps : ℝ) (k : ℕ)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (he : 0 < eps) (he1 : eps ≤ 1)
    (hk : 15 ≤ (k:ℝ)*eps) :
    alpha-eps ≤ (1-eps/3)*(1-eps/3)*alpha*(k:ℝ)/((k:ℝ)+5) := by
  have kp : 0 < (k:ℝ)+5 := by positivity
  apply (le_div_iff₀ kp).mpr
  have t1 : 0 ≤ alpha*eps^2*(k:ℝ) := by positivity
  have t2 : 0 ≤ (1-alpha)*eps*(k:ℝ) := mul_nonneg (mul_nonneg (by linarith) he.le) (by positivity)
  have t3 : 0 ≤ (1-alpha)*5 := mul_nonneg (by linarith) (by norm_num)
  nlinarith
end RobustMatching.R4WeightComposition
#print axioms RobustMatching.R4WeightComposition.weighted_interval_budget
#print axioms RobustMatching.R4WeightComposition.assemble
#print axioms RobustMatching.R4WeightComposition.accuracy_budget
