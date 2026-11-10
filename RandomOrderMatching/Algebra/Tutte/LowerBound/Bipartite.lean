import RandomOrderMatching.Algebra.Tutte.LowerBound

/-! Genuine weighted Tutte minors on disjoint row and column vertex sets.
Their chosen diagonal is a bipartite matching, so independent unordered
edge variables isolate it even though the two Tutte orientations share a
variable. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Algebra.Tutte.LowerBound
set_option linter.unusedSectionVars false
open RandomOrderMatching.Algebra.Tutte
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [LinearOrder V]

@[simp] theorem toRat_C (p : Coeff (Sym2 V)) :
    toRat (Polynomial.C p) = RatFunc.C (algebraMap (Coeff (Sym2 V)) (EdgeField V) p) := by
  simp [toRat, RatFunc.algebraMap_C]

@[simp] theorem toRat_X :
    toRat (Polynomial.X : Polynomial (Coeff (Sym2 V))) = RatFunc.X := by
  simp [toRat, RatFunc.algebraMap_X]

theorem unordered_matching_separation (row col : ι → V)
    (hr : Function.Injective row) (hc : Function.Injective col)
    (hd : ∀ i j, row i ≠ col j) :
    ∀ i j k, s(row i, col j) = s(row k, col k) → i = j := by
  intro i j k he
  rcases Sym2.eq_iff.mp he with h | h
  · exact (hr h.1).trans (hc h.2).symm
  · exact (hd i k h.1).elim

def tutteSign (G : SimpleGraph V) (u v : V) : ℚ := by
  classical
  exact if G.Adj u v then if u < v then 1 else -1 else 0

theorem mapped_polynomialMatrix_tutte (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (row col : ι → V) :
    (toRat (E := Sym2 V)).mapMatrix
      (polynomialMatrix (fun i j => s(row i,col j))
        (fun i j => tutteSign G (row i) (col j))
        (fun i j => w s(row i,col j))) =
      (weightedTutte G w).submatrix row col := by
  classical
  funext i j
  by_cases ha : G.Adj (row i) (col j)
  · by_cases hl : row i < col j
    · simp [polynomialMatrix, tutteSign, weightedTutte, weightedVariable,
        edgeVariable, ha, hl, RingHom.mapMatrix_apply]
    · simp [polynomialMatrix, tutteSign, weightedTutte, weightedVariable,
        edgeVariable, ha, hl, RingHom.mapMatrix_apply, Sym2.eq_swap]
  · simp [polynomialMatrix, tutteSign, weightedTutte, ha, RingHom.mapMatrix_apply]

/-- The weight of every prescribed bipartite matching occurs below the
degree of the corresponding actual weighted-Tutte minor. -/
theorem tutte_bipartite_matching_lower (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (row col : ι → V) (hr : Function.Injective row) (hc : Function.Injective col)
    (hd : ∀ i j, row i ≠ col j) (hadj : ∀ i, G.Adj (row i) (col i)) :
    ((weightedTutte G w).submatrix row col).det ≠ 0 ∧
    (∑ i, (w s(row i,col i) : ℤ)) ≤
      ((weightedTutte G w).submatrix row col).det.intDegree := by
  have hs := unordered_matching_separation row col hr hc hd
  have hn : ∀ i, tutteSign G (row i) (col i) ≠ 0 := by
    intro i
    simp [tutteSign, hadj i]
    split_ifs <;> norm_num
  have hh := rational_det_matching_lower (fun i j => s(row i,col j)) hs
    (fun i j => tutteSign G (row i) (col j)) hn (fun i j => w s(row i,col j))
  rw [mapped_polynomialMatrix_tutte] at hh
  exact hh


/-- A bipartite host allows a square partial-permutation minor to split
into two generic bipartite matching matrices. The row/column sets may overlap. -/
theorem tutte_bipartite_partial_permutation_lower
    (G : SimpleGraph V) (w : Sym2 V → ℕ) (L : Finset V)
    (hcross : ∀ u v, G.Adj u v → (u ∈ L ∧ v ∉ L) ∨ (u ∉ L ∧ v ∈ L))
    (row col : ι → V) (hr : Function.Injective row) (hc : Function.Injective col)
    (hadj : ∀ i, G.Adj (row i) (col i)) :
    ((weightedTutte G w).submatrix row col).det ≠ 0 ∧
    (∑ i, (w s(row i,col i) : ℤ)) ≤
      ((weightedTutte G w).submatrix row col).det.intDegree := by
  classical
  let P : ι → Prop := fun i => row i ∈ L
  let e := Equiv.sumCompl P
  let A := (weightedTutte G w).submatrix row col
  let B : Matrix {i // P i} {i // P i} (RatFunc (EdgeField V)) := A.submatrix Subtype.val Subtype.val
  let C : Matrix {i // ¬ P i} {i // ¬ P i} (RatFunc (EdgeField V)) := A.submatrix Subtype.val Subtype.val
  have hside : ∀ i, col i ∈ L ↔ row i ∉ L := by
    intro i
    rcases hcross _ _ (hadj i) with h | h <;> tauto
  have hz : ∀ u v, (u ∈ L ↔ v ∈ L) → weightedTutte G w u v = 0 := by
    intro u v he
    have hn : ¬ G.Adj u v := by
      intro hh
      rcases hcross u v hh with h | h <;> tauto
    simp [weightedTutte, hn]
  have hblock : A.submatrix e e = Matrix.fromBlocks B 0 0 C := by
    funext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · change weightedTutte G w (row i.val) (col j.val) = 0
      apply hz
      have hi : row i.val ∈ L := i.prop
      have hj : col j.val ∈ L := (hside j.val).mpr j.prop
      tauto
    · change weightedTutte G w (row i.val) (col j.val) = 0
      apply hz
      have hi : row i.val ∉ L := i.prop
      have hj : col j.val ∉ L := by
        intro hh
        exact (hside j.val).mp hh j.prop
      tauto
    · rfl
  have hB := tutte_bipartite_matching_lower G w
    (fun i : {i // P i} => row i.val) (fun i : {i // P i} => col i.val)
    (hr.comp Subtype.val_injective) (hc.comp Subtype.val_injective)
    (by
      intro i j he
      have hj : col j.val ∉ L := by
        intro hh
        exact (hside j.val).mp hh j.prop
      exact hj (he ▸ i.prop))
    (fun i => hadj i.val)
  have hC := tutte_bipartite_matching_lower G w
    (fun i : {i // ¬ P i} => row i.val) (fun i : {i // ¬ P i} => col i.val)
    (hr.comp Subtype.val_injective) (hc.comp Subtype.val_injective)
    (by
      intro i j he
      have hj : col j.val ∈ L := (hside j.val).mpr j.prop
      apply i.prop
      change row i.val ∈ L
      rw [he]
      exact hj)
    (fun i => hadj i.val)
  have hdet : A.det = B.det * C.det := by
    rw [← Matrix.det_submatrix_equiv_self e A, hblock]
    simp [Matrix.det_fromBlocks_zero₂₁]
  change A.det ≠ 0 ∧ _ ≤ A.det.intDegree
  have hBn : B.det ≠ 0 := hB.1
  have hCn : C.det ≠ 0 := hC.1
  constructor
  · rw [hdet]
    exact mul_ne_zero hBn hCn
  · rw [hdet, RatFunc.intDegree_mul hBn hCn]
    have hs : (∑ i, (w s(row i,col i) : ℤ)) =
        (∑ i : {i // P i}, (w s(row i.val,col i.val) : ℤ)) +
        (∑ i : {i // ¬ P i}, (w s(row i.val,col i.val) : ℤ)) := by
      rw [← Equiv.sum_comp e]
      simp [Fintype.sum_sum_type, e]
    rw [hs]
    exact add_le_add hB.2 hC.2

end RandomOrderMatching.Algebra.Tutte.LowerBound
#print axioms RandomOrderMatching.Algebra.Tutte.LowerBound.tutte_bipartite_matching_lower
