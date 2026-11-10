import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic

/-!
Concrete determinant foundations for prescribed-subset exchange.
No matching theorem or exchange inequality is assumed in this file.
-/
noncomputable section
open scoped BigOperators
open Matrix Finset

namespace RandomOrderMatching.Algebra

set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

variable {n R K : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Keep precisely the two diagonal rectangles determined by row and column sets. -/
def rectMask (M : Matrix n n R) (S T : Finset n) : Matrix n n R :=
  fun i j => if (i ∈ S ↔ j ∈ T) then M i j else 0

/-- Generalized Laplace expansion before factoring the two rectangles.
Unlike an assumed exchange axiom, this is a direct determinant identity. -/
theorem det_eq_sum_rectMask (M : Matrix n n R) (S : Finset n) :
    M.det = ∑ T : Finset n, (rectMask M S T).det := by
  let A : Matrix n n R := fun i j => if j ∈ S then M.transpose i j else 0
  let B : Matrix n n R := fun i j => if j ∈ S then 0 else M.transpose i j
  have hab : A + B = M.transpose := by
    ext i j
    change A i j + B i j = M.transpose i j
    by_cases hj : j ∈ S <;> simp [A, B, hj]
  have h := (Matrix.detRowAlternating :
    (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap.map_add_univ A B
  change (A+B).det = ∑ T : Finset n, Matrix.det (T.piecewise A B) at h
  rw [hab, Matrix.det_transpose] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro T _
  have hm : T.piecewise A B = (rectMask M S T).transpose := by
    ext i j
    by_cases hi : j ∈ S <;> by_cases hj : i ∈ T <;>
      simp [rectMask, Matrix.transpose_apply, Finset.piecewise, A, B, hi, hj]
  rw [hm, Matrix.det_transpose]

/-- Normalized exchanged first basis: retain identity columns outside S. -/
def firstExchange (M : Matrix n n R) (S : Finset n) : Matrix n n R :=
  fun i j => if j ∈ S then M i j else (1 : Matrix n n R) i j

/-- Normalized exchanged second basis: replace columns in S by identity columns. -/
def secondExchange (M : Matrix n n R) (S : Finset n) : Matrix n n R :=
  fun i j => if j ∈ S then (1 : Matrix n n R) i j else M i j

def mixedColumns (A B : Matrix n n R) (S : Finset n) : Matrix n n R :=
  fun i j => if j ∈ S then B i j else A i j

theorem mul_firstExchange (A M : Matrix n n R) (S : Finset n) :
    A * firstExchange M S = mixedColumns A (A*M) S := by
  ext i j
  by_cases hj : j ∈ S
  · simp [Matrix.mul_apply, firstExchange, mixedColumns, hj]
  · simp [Matrix.mul_apply, firstExchange, mixedColumns, hj, Matrix.one_apply]

theorem mul_secondExchange (A M : Matrix n n R) (S : Finset n) :
    A * secondExchange M S = mixedColumns (A*M) A S := by
  ext i j
  by_cases hj : j ∈ S
  · simp [Matrix.mul_apply, secondExchange, mixedColumns, hj, Matrix.one_apply]
  · simp [Matrix.mul_apply, secondExchange, mixedColumns, hj]

/-- A diagonal-rectangle determinant is exactly the exchanged determinant product. -/
theorem det_rectMask_self (M : Matrix n n R) (S : Finset n) :
    (rectMask M S S).det =
      (firstExchange M S).det * (secondExchange M S).det := by
  let e := Equiv.sumCompl (fun x : n => x ∈ S)
  let P : Matrix {x // x ∈ S} {x // x ∈ S} R := M.submatrix Subtype.val Subtype.val
  let Q : Matrix {x // x ∉ S} {x // x ∉ S} R := M.submatrix Subtype.val Subtype.val
  let U : Matrix {x // x ∈ S} {x // x ∉ S} R := M.submatrix Subtype.val Subtype.val
  let L : Matrix {x // x ∉ S} {x // x ∈ S} R := M.submatrix Subtype.val Subtype.val
  have hm : (rectMask M S S).submatrix e e = Matrix.fromBlocks P 0 0 Q := by
    ext (i | i) (j | j) <;> simp [rectMask, e, P, Q, i.prop, j.prop]
  have ha : (firstExchange M S).submatrix e e = Matrix.fromBlocks P 0 L 1 := by
    ext (i | i) (j | j)
    · simp [firstExchange, e, P, j.prop]
    · have hne : (i : n) ≠ (j : n) := fun h => j.prop (h ▸ i.prop)
      simp [firstExchange, e, j.prop, Matrix.one_apply, hne]
    · simp [firstExchange, e, L, j.prop]
    · simp +instances only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inr,
        firstExchange, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
        Subtype.ext_iff]
      rw [if_neg j.prop]
  have hb : (secondExchange M S).submatrix e e = Matrix.fromBlocks 1 U 0 Q := by
    ext (i | i) (j | j)
    · simp +instances only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inl,
        secondExchange, Matrix.fromBlocks_apply₁₁, Matrix.one_apply,
        Subtype.ext_iff]
      rw [if_pos j.prop]
    · simp [secondExchange, e, U, j.prop]
    · have hne : (i : n) ≠ (j : n) := fun h => i.prop (h ▸ j.prop)
      simp [secondExchange, e, j.prop, Matrix.one_apply, hne]
    · simp [secondExchange, e, Q, j.prop]
  rw [← Matrix.det_submatrix_equiv_self e (rectMask M S S), hm,
    ← Matrix.det_submatrix_equiv_self e (firstExchange M S), ha,
    ← Matrix.det_submatrix_equiv_self e (secondExchange M S), hb]
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]

/-- A surviving Leibniz term supplies the precise row/column bijection. -/
theorem exists_rectMask_permutation (M : Matrix n n R) (S T : Finset n)
    (hne : (rectMask M S T).det ≠ 0) :
    ∃ σ : Equiv.Perm n, ∀ j, (σ j ∈ S ↔ j ∈ T) := by
  classical
  rw [Matrix.det_apply'] at hne
  obtain ⟨σ, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨σ, ?_⟩
  intro j
  by_contra hj
  have hzero : rectMask M S T (σ j) j = 0 := by simp [rectMask, hj]
  have hz : (∏ i, rectMask M S T (σ i) i) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hzero
  exact hs (by simp [hz])

section RationalFunctions
variable [Field K]

/-- A nonzero finite sum has a nonzero summand of at least its degree.
The zero convention of `RatFunc.intDegree` is handled explicitly. -/
theorem exists_intDegree_summand {ι : Type*} (s : Finset ι)
    (f : ι → RatFunc K) (hne : (∑ i ∈ s, f i) ≠ 0) :
    ∃ i ∈ s, f i ≠ 0 ∧ (∑ i ∈ s, f i).intDegree ≤ (f i).intDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at hne ⊢
    by_cases hfs : (∑ i ∈ s, f i) = 0
    · refine ⟨a, Finset.mem_insert_self _ _, ?_, ?_⟩
      · simpa [hfs] using hne
      · simp [hfs]
    · by_cases hfa : f a = 0
      · obtain ⟨i, hi, hfi, hdeg⟩ := ih hfs
        exact ⟨i, Finset.mem_insert_of_mem hi, hfi, by simpa [hfa] using hdeg⟩
      · have hh := RatFunc.intDegree_add_le hfs hne
        rcases le_max_iff.mp hh with hh | hh
        · exact ⟨a, Finset.mem_insert_self _ _, hfa, hh⟩
        · obtain ⟨i, hi, hfi, hdeg⟩ := ih hfs
          exact ⟨i, Finset.mem_insert_of_mem hi, hfi, hh.trans hdeg⟩

theorem intDegree_det_permute (M : Matrix n n (RatFunc K)) (σ : Equiv.Perm n) :
    ((M.submatrix id σ).det).intDegree = M.det.intDegree := by
  rw [Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem det_permute_ne_zero (M : Matrix n n (RatFunc K)) (σ : Equiv.Perm n)
    (hne : M.det ≠ 0) : (M.submatrix id σ).det ≠ 0 := by
  rw [Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simpa [h] using hne

/-- Actual normalized prescribed-subset determinant exchange, for every
finite row set. Its proof derives both nonsingularity and the valuation
inequality from the determinant expansion; neither is assumed. -/
theorem normalized_multiple_exchange (M : Matrix n n (RatFunc K))
    (S : Finset n) (hne : M.det ≠ 0) :
    ∃ σ : Equiv.Perm n,
      (firstExchange (M.submatrix id σ) S).det ≠ 0 ∧
      (secondExchange (M.submatrix id σ) S).det ≠ 0 ∧
      M.det.intDegree ≤
        ((firstExchange (M.submatrix id σ) S).det).intDegree +
        ((secondExchange (M.submatrix id σ) S).det).intDegree := by
  have hexp := det_eq_sum_rectMask M S
  have hsum : (∑ T : Finset n, (rectMask M S T).det) ≠ 0 := by
    rwa [← hexp]
  obtain ⟨T, _, hT, hdeg⟩ :=
    exists_intDegree_summand Finset.univ (fun T : Finset n => (rectMask M S T).det) hsum
  rw [← hexp] at hdeg
  obtain ⟨π, hπ⟩ := exists_rectMask_permutation M S T hT
  have hm : (rectMask M S T).submatrix id π.symm =
      rectMask (M.submatrix id π.symm) S S := by
    ext i j
    have ht : (π.symm j ∈ T ↔ j ∈ S) := by simpa using (hπ (π.symm j)).symm
    simp only [Matrix.submatrix_apply, id_eq, rectMask, ht]
  have hnon := det_permute_ne_zero (rectMask M S T) π.symm hT
  rw [hm, det_rectMask_self] at hnon
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hnon
  refine ⟨π.symm, ha, hb, ?_⟩
  have hd := intDegree_det_permute (rectMask M S T) π.symm
  rw [hm, det_rectMask_self, RatFunc.intDegree_mul ha hb] at hd
  exact hdeg.trans_eq hd.symm

/-- Prescribed-subset exchange for two actual nonsingular rational-function
matrices. Columns are kept ordered, so no ordering signs need be assumed. -/
theorem matrix_multiple_exchange (A B : Matrix n n (RatFunc K))
    (S : Finset n) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    ∃ σ : Equiv.Perm n,
      (mixedColumns A (B.submatrix id σ) S).det ≠ 0 ∧
      (mixedColumns (B.submatrix id σ) A S).det ≠ 0 ∧
      A.det.intDegree + B.det.intDegree ≤
        ((mixedColumns A (B.submatrix id σ) S).det).intDegree +
        ((mixedColumns (B.submatrix id σ) A S).det).intDegree := by
  let M := A⁻¹ * B
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hAM : A * M = B := Matrix.mul_nonsing_inv_cancel_left A B hunit
  have hdet : A.det * M.det = B.det := by rw [← Matrix.det_mul, hAM]
  have hM : M.det ≠ 0 := by
    intro hm
    exact hB (by rw [← hdet, hm, mul_zero])
  obtain ⟨σ, hp, hq, hdeg⟩ := normalized_multiple_exchange M S hM
  have hperm : A * (M.submatrix id σ) = B.submatrix id σ := by
    have hh := Matrix.submatrix_mul_equiv A M id (Equiv.refl n) σ
    simpa [hAM] using hh
  have hpEq : A * firstExchange (M.submatrix id σ) S =
      mixedColumns A (B.submatrix id σ) S := by rw [mul_firstExchange, hperm]
  have hqEq : A * secondExchange (M.submatrix id σ) S =
      mixedColumns (B.submatrix id σ) A S := by rw [mul_secondExchange, hperm]
  refine ⟨σ, ?_, ?_, ?_⟩
  · rw [← hpEq, Matrix.det_mul]
    exact mul_ne_zero hA hp
  · rw [← hqEq, Matrix.det_mul]
    exact mul_ne_zero hA hq
  · have hn := RatFunc.intDegree_mul hA hM
    rw [hdet] at hn
    rw [← hpEq, ← hqEq, Matrix.det_mul, Matrix.det_mul,
      RatFunc.intDegree_mul hA hp, RatFunc.intDegree_mul hA hq]
    linarith

end RationalFunctions

end RandomOrderMatching.Algebra
