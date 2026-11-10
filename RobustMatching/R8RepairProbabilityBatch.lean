import RobustMatching.R8RepairProbabilityClocks

/-! Concentration on original-label coordinates, with explicit copy grouping.
No independence assumption is imposed on individual copies. -/
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RobustMatching.R8RepairProbability

variable {B T : Type*} [Fintype B] [Fintype T]

def blockValue (parent : T → B) (X : T → Clock → ℝ) (b : B) (z : Clock) : ℝ :=
  ∑ i with parent i = b, X i z

def blockRange (parent : T → B) (a : T → ℝ) (b : B) : ℝ :=
  ∑ i with parent i = b, a i

lemma block_sum (parent : T → B) (X : T → Clock → ℝ) (z : B → Clock) :
    ∑ b, blockValue parent X b (z b) = ∑ i, X i (z (parent i)) := by
  simp only [blockValue, Finset.sum_filter]
  rw [Finset.sum_comm]
  congr 1
  funext i
  simp

lemma block_range_sum (parent : T → B) (a : T → ℝ) :
    ∑ b, blockRange parent a b = ∑ i, a i := by
  simpa [blockRange, blockValue] using block_sum parent (fun i _ => a i) (fun _ => 0)

lemma integral_clock_sum (s : Finset T) (X : T → Clock → ℝ) :
    ∫ z, (∑ i ∈ s, X i z) ∂clockMeasure =
      ∑ i ∈ s, ∫ z, X i z ∂clockMeasure := by
  simp only [integral_clock, Finset.mul_sum, Finset.sum_add_distrib]

lemma block_mean_sum (parent : T → B) (X : T → Clock → ℝ) :
    ∑ b, ∫ z, blockValue parent X b z ∂clockMeasure =
      ∑ i, ∫ z, X i z ∂clockMeasure := by
  simp only [blockValue, integral_clock_sum]
  exact block_range_sum parent (fun i => ∫ z, X i z ∂clockMeasure)

lemma block_bounds (parent : T → B) (X : T → Clock → ℝ) (a : T → ℝ)
    (h : ∀ i z, X i z ∈ Set.Icc 0 (a i)) (b : B) (z : Clock) :
    blockValue parent X b z ∈ Set.Icc 0 (blockRange parent a b) := by
  constructor
  · exact Finset.sum_nonneg fun i _ => (h i z).1
  · exact Finset.sum_le_sum fun i _ => (h i z).2

/-- Upper tail for actual sums of copied variables sharing their parent clock. -/
theorem batch_upper_tail (parent : T → B) (X : T → Clock → ℝ) (a : T → ℝ)
    (h : ∀ i z, X i z ∈ Set.Icc 0 (a i)) {t : ℝ} (ht : 0 ≤ t) :
    (experiment (B := B)).real
      {z | t ≤ (∑ i, X i (z (parent i))) - (∑ i, ∫ u, X i u ∂clockMeasure)} ≤
      Real.exp (-2*t^2 / ∑ b, (blockRange parent a b)^2) := by
  have he := product_bounded_upper_tail (fun _ : B => clockMeasure)
    (blockValue parent X) (blockRange parent a)
    (fun _ => measurable_of_finite _) (block_bounds parent X a h) ht
  simpa only [Finset.sum_sub_distrib, block_sum, block_mean_sum, experiment] using he

/-- Lower tail for those same original-label coordinates. -/
theorem batch_lower_tail (parent : T → B) (X : T → Clock → ℝ) (a : T → ℝ)
    (h : ∀ i z, X i z ∈ Set.Icc 0 (a i)) {t : ℝ} (ht : 0 ≤ t) :
    (experiment (B := B)).real
      {z | t ≤ (∑ i, ∫ u, X i u ∂clockMeasure) - (∑ i, X i (z (parent i)))} ≤
      Real.exp (-2*t^2 / ∑ b, (blockRange parent a b)^2) := by
  have hb : ∀ i z, a i-X i z ∈ Set.Icc 0 (a i) := by
    intro i z
    have hh := h i z
    constructor <;> linarith [hh.1,hh.2]
  have hi (i) : (∫ u, a i-X i u ∂clockMeasure) = a i-(∫ u, X i u ∂clockMeasure) := by
    rw [integral_clock,integral_clock]
    ring
  have he := batch_upper_tail parent (fun i z => a i-X i z) a hb ht
  simpa only [hi, Finset.sum_sub_distrib, sub_sub_sub_cancel_left] using he

/-- The square-range budget depends on the largest original block, not the
number of copies treated falsely as independent. -/
theorem batch_square_budget (parent : T → B) (a : T → ℝ) (k : ℕ)
    (hcard : ∀ b, (Finset.univ.filter (fun i => parent i = b)).card ≤ k)
    {D : ℝ} (ha : ∀ i, 0 ≤ a i) (hD : ∀ i, a i ≤ D) :
    ∑ b, (blockRange parent a b)^2 ≤ (k:ℝ)*D*(∑ i, a i) := by
  have hsq := grouped_sum_sq_le (fun b => Finset.univ.filter (fun i => parent i=b)) a k hcard
  have hf : (∑ b, ∑ i ∈ Finset.univ.filter (fun i => parent i=b), a i^2) = ∑ i, a i^2 :=
    block_range_sum parent (fun i => a i^2)
  rw [hf] at hsq
  have hterm : (∑ i, a i^2) ≤ D*(∑ i, a i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by nlinarith [ha i,hD i]
  calc
    _ ≤ (k:ℝ)*(∑ i,a i^2) := hsq
    _ ≤ (k:ℝ)*(D*(∑ i,a i)) := mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg k)
    _ = _ := by ring

/-- A finite union bound retains every event's actual map. -/
theorem bad_union_bound {E : Type*} [Fintype E]
    (bad : E → Set (B → Clock)) (bound : E → ℝ)
    (h : ∀ e, (experiment (B := B)).real (bad e) ≤ bound e) :
    (experiment (B := B)).real (⋃ e, bad e) ≤ ∑ e, bound e :=
  (measureReal_iUnion_fintype_le bad).trans (Finset.sum_le_sum fun e _ => h e)

end RobustMatching.R8RepairProbability
