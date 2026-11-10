import RobustMatching.R7ReductionAccuracy
import RobustMatching.R3Precision

/-! Finite black-box compiler theorem. All outputs are the concrete greedy
matchings. The approximation premise is solely the local band algorithm's
matching guarantee, as appropriate for a reduction. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7ReductionCompiler
open RobustMatching.R2Cut RobustMatching.R7ReductionGreedy
open RobustMatching.R7ReductionShifts
variable {V : Type*} [DecidableEq V]

theorem local_rounding_transfer (M N : Graph V) (w : Edge V → ℝ)
    {alpha eta L : ℝ} (ha : 0 ≤ alpha) (heta : 0 < eta) (hL : 0 < L)
    (hw : ∀ e,0 ≤ w e) (hML : ∀ e ∈ M,L ≤ w e)
    (hlocal : alpha*(∑ e ∈ M,RobustMatching.R3Precision.rounded (eta*L) (w e)) ≤
      ∑ e ∈ N,RobustMatching.R3Precision.rounded (eta*L) (w e)) :
    alpha*(1-eta)*(∑ e ∈ M,w e) ≤ ∑ e ∈ N,w e := by
  have hlo : (1-eta)*(∑ e ∈ M,w e) ≤
      ∑ e ∈ M,RobustMatching.R3Precision.rounded (eta*L) (w e) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have h := (RobustMatching.R3Precision.rounded_bounds (mul_pos heta hL) (hw e)).1
    have hm := mul_le_mul_of_nonneg_left (hML e he) heta.le
    linarith
  have hu : (∑ e ∈ N,RobustMatching.R3Precision.rounded (eta*L) (w e)) ≤
      ∑ e ∈ N,w e := Finset.sum_le_sum (fun e he =>
    (RobustMatching.R3Precision.rounded_bounds (mul_pos heta hL) (hw e)).2)
  have hl := mul_le_mul_of_nonneg_left hlo ha
  nlinarith

theorem shifted_compiler (M : Graph V) (w : Edge V → ℝ)
    {q : ℕ} (hq : 0 < q) (drop : Edge V → Fin q)
    (levels : Fin q → ℕ → Graph V) (count : Fin q → ℕ)
    (index : Fin q → Edge V → ℕ) (scale : Fin q → ℝ)
    {alpha r B : ℝ} (ha : 0 ≤ alpha) (hr : 0 < r) (hr1 : r < 1) (hB : 0 < B)
    (hscale : ∀ s,0 ≤ scale s)
    (hindex : ∀ s i, i < count s → ∀ e ∈ levels s i,index s e = i)
    (hsource : ∀ s e,e ∈ kept M drop s → index s e < count s)
    (hmatch : ∀ s i,Matching (levels s i))
    (hweights : ∀ s i,i < count s → ∀ e ∈ levels s i,
      scale s*r^i ≤ w e ∧ w e ≤ scale s*r^i/(B*r))
    (hlocal : ∀ s i,i < count s →
      alpha*(∑ e ∈ (kept M drop s).filter (fun e => index s e = i),w e) ≤
        ∑ e ∈ levels s i,w e) :
    ∃ s : Fin q, Matching (combine (levels s) (count s)) ∧
      (alpha*(((q:ℝ)-1)/(q:ℝ))/(1+2/(B*(1-r))))*(∑ e ∈ M,w e) ≤
        ∑ e ∈ combine (levels s) (count s),w e := by
  obtain ⟨s,hs⟩ := exists_good_shift M w hq drop
  refine ⟨s,combine_matching (levels s) (hmatch s) (count s),?_⟩
  have hlocalout := local_to_greedy (kept M drop s) (levels s) (count s)
    (index s) (hindex s) (hsource s) (hmatch s) w hr hr1 (hscale s) hB
    (hweights s) (hlocal s)
  have hc : 0 ≤ alpha/(1+2/(B*(1-r))) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hc
  calc
    _ = (alpha/(1+2/(B*(1-r))))*
        ((((q:ℝ)-1)/(q:ℝ))*(∑ e ∈ M,w e)) := by ring
    _ ≤ (alpha/(1+2/(B*(1-r))))*(∑ e ∈ kept M drop s,w e) := hh
    _ ≤ _ := hlocalout

end RobustMatching.R7ReductionCompiler

#print axioms RobustMatching.R7ReductionCompiler.local_rounding_transfer
#print axioms RobustMatching.R7ReductionCompiler.shifted_compiler
