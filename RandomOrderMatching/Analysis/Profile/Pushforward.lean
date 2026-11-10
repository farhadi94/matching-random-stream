import RandomOrderMatching.Graph.Basic
import RandomOrderMatching.Analysis.Support.PairMoments

/-! Actual finite graph/atom identities for the typed interval map.
These lemmas count vertices and incidences; they do not assume the final
matrix equalities. The concrete semantic row instantiation is separate. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Graph

def pushMass {X K : Type*} [DecidableEq K]
    (A : Finset X) (tag : X → K) (w : X → ℝ) (k : K) : ℝ :=
  ∑ x ∈ A, if tag x=k then w x else 0

theorem pushMass_nonneg {X K : Type*} [DecidableEq K]
    (A : Finset X) (tag : X → K) (w : X → ℝ)
    (hw : ∀ x ∈ A, 0 ≤ w x) (k : K) :
    0 ≤ pushMass A tag w k := by
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact hw x hx
  · rfl

theorem pushMass_eval {X K : Type*} [DecidableEq K] [Fintype K]
    (A : Finset X) (tag : X → K) (w : X → ℝ) (cost : K → ℝ) :
    (∑ k, cost k * pushMass A tag w k) =
      ∑ x ∈ A, cost (tag x)*w x := by
  simp only [pushMass, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [eq_comm]

theorem pushMass_total {X K : Type*} [DecidableEq K] [Fintype K]
    (A : Finset X) (tag : X → K) (w : X → ℝ) :
    (∑ k, pushMass A tag w k) = ∑ x ∈ A, w x := by
  simpa using pushMass_eval A tag w (fun _ => 1)

theorem pushMass_forbidden_zero {X K : Type*} [DecidableEq K]
    (A : Finset X) (tag : X → K) (w : X → ℝ) (allowed : K → Prop)
    (ha : ∀ x ∈ A, allowed (tag x)) (k : K) (hk : ¬allowed k) :
    pushMass A tag w k = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hne : tag x ≠ k := fun h => hk (h ▸ ha x hx)
  simp [hne]

theorem pushMass_bounds {X K : Type*} [DecidableEq K]
    (A : Finset X) (tag : X → K) (w degree : X → ℝ)
    (lo hi : K → ℝ) (hw : ∀ x ∈ A, 0 ≤ w x)
    (hlo : ∀ x ∈ A, lo (tag x) ≤ degree x)
    (hhi : ∀ x ∈ A, degree x ≤ hi (tag x)) (k : K) :
    lo k*pushMass A tag w k ≤ pushMass A tag (fun x => degree x*w x) k ∧
    pushMass A tag (fun x => degree x*w x) k ≤ hi k*pushMass A tag w k := by
  constructor
  · simp only [pushMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    by_cases h : tag x=k
    · simp only [h, if_true]
      exact mul_le_mul_of_nonneg_right (by simpa [h] using hlo x hx) (hw x hx)
    · simp [h]
  · simp only [pushMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    by_cases h : tag x=k
    · simp only [h, if_true]
      exact mul_le_mul_of_nonneg_right (by simpa [h] using hhi x hx) (hw x hx)
    · simp [h]

section ActualGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

def incidenceDegree (H : Graph V) (v : V) : ℝ :=
  ∑ e ∈ H, if v ∈ e.val then 1 else 0

theorem incidenceDegree_nonneg (H : Graph V) (v : V) :
    0 ≤ incidenceDegree H v := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> norm_num

theorem incidenceDegree_eq_card (H : Graph V) (v : V) :
    incidenceDegree H v = ((H.filter fun e => v ∈ e.val).card : ℝ) := by
  simp only [incidenceDegree, Finset.sum_boole]

/-- A class's actual graph degree equals its total edge-endpoint incidence,
including two incidences on an edge whose endpoints have that class. -/
theorem incidence_weighted_sum (H : Graph V) (f : V → ℝ) :
    (∑ v, f v*incidenceDegree H v) = ∑ e ∈ H, ∑ v ∈ e.val, f v := by
  simp only [incidenceDegree, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [← Finset.sum_filter]

theorem incidence_class_sum {K : Type*} [DecidableEq K]
    (H : Graph V) (tag : V → K) (k : K) :
    pushMass Finset.univ tag (incidenceDegree H) k =
      ∑ e ∈ H, ∑ v ∈ e.val, if tag v=k then 1 else 0 := by
  have hh := incidence_weighted_sum H (fun v => if tag v=k then 1 else 0)
  simpa [pushMass, ite_mul] using hh

theorem incidence_total (H : Graph V) :
    (∑ v, incidenceDegree H v) = 2*(H.card : ℝ) := by
  have hh := incidence_weighted_sum H (fun _ => 1)
  simp only [one_mul] at hh
  rw [hh]
  calc
    (∑ e ∈ H, ∑ _v ∈ e.val, (1 : ℝ)) = ∑ _e ∈ H, (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      simp [e.property]
    _ = 2*(H.card : ℝ) := by simp; ring

/-- Matching endpoint balances are an actual disjoint-union identity. -/
theorem matching_endpoint_sum (M : Graph V) (hM : Matching M) (f : V → ℝ) :
    (∑ v ∈ covered M, f v) = ∑ e ∈ M, ∑ v ∈ e.val, f v := by
  rw [covered, Finset.sum_biUnion hM]

theorem matching_degree_lower (M : Graph V) (hM : Matching M)
    (a : V → ℝ) (eta : ℝ)
    (hdegree : ∀ e ∈ M, 1-eta ≤ ∑ v ∈ e.val, a v) :
    (1-eta)*(M.card : ℝ) ≤ ∑ v ∈ covered M, a v := by
  rw [matching_endpoint_sum M hM a]
  calc
    (1-eta)*(M.card : ℝ) = ∑ _e ∈ M, (1-eta) := by simp; ring
    _ ≤ ∑ e ∈ M, ∑ v ∈ e.val, a v := Finset.sum_le_sum hdegree

theorem positive_degree_count (A : Finset V) (a : V → ℝ) (h b : ℝ)
    (hh : 0 < h) (ha : ∀ v, 0 ≤ a v)
    (hlower : ∀ v ∈ A, h ≤ a v) (htotal : (∑ v, a v) ≤ b) :
    (A.card : ℝ) ≤ b/h := by
  apply (le_div_iff₀ hh).2
  calc
    (A.card : ℝ)*h = ∑ _v ∈ A, h := by simp
    _ ≤ ∑ v ∈ A, a v := Finset.sum_le_sum hlower
    _ ≤ ∑ v, a v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ A) (fun v _ _ => ha v)
    _ ≤ b := htotal

end ActualGraph
end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.pushMass_eval
#print axioms RandomOrderMatching.Analysis.Profile.incidence_class_sum
#print axioms RandomOrderMatching.Analysis.Profile.matching_degree_lower
#print axioms RandomOrderMatching.Analysis.Profile.positive_degree_count
