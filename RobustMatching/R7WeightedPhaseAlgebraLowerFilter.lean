import RobustMatching.R7WeightedPhaseAlgebraLowerTutte

/-! Deleting edge variables cannot raise the polynomial determinant degree.
This safely specializes before entering the fraction field; an evaluation
homomorphism is never incorrectly extended to arbitrary rational functions. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7WeightedPhaseAlgebraLower
open RobustMatching.R7AlgebraTutte
set_option linter.unusedSectionVars false
variable {ι E V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [LinearOrder V]

def variableFilter (p : E → Prop) : Coeff E →+* Coeff E := by
  classical
  exact MvPolynomial.eval₂Hom MvPolynomial.C (fun e => if p e then MvPolynomial.X e else 0)

theorem filter_polynomialMatrix (p : E → Prop) [DecidablePred p] (edge : ι → ι → E)
    (a : ι → ι → ℚ) (w : ι → ι → ℕ) :
    (Polynomial.mapRingHom (variableFilter p)).mapMatrix (polynomialMatrix edge a w) =
      polynomialMatrix edge (fun i j => if p (edge i j) then a i j else 0) w := by
  classical
  funext i j
  by_cases hp : p (edge i j) <;>
    simp [polynomialMatrix, variableFilter, hp, RingHom.mapMatrix_apply]

theorem tutte_minor_restriction (G H : SimpleGraph V) (w : Sym2 V → ℕ)
    (p : Sym2 V → Prop)
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ p s(u,v))
    (row col : ι → V)
    (hn : ((weightedTutte H w).submatrix row col).det ≠ 0) :
    ((weightedTutte G w).submatrix row col).det ≠ 0 ∧
    ((weightedTutte H w).submatrix row col).det.intDegree ≤
      ((weightedTutte G w).submatrix row col).det.intDegree := by
  classical
  let edge := fun i j => s(row i,col j)
  let weights := fun i j => w (edge i j)
  let PG := polynomialMatrix edge (fun i j => tutteSign G (row i) (col j)) weights
  let PH := polynomialMatrix edge (fun i j => tutteSign H (row i) (col j)) weights
  let f := variableFilter p
  have hs : ∀ u v, tutteSign H u v = if p s(u,v) then tutteSign G u v else 0 := by
    intro u v
    by_cases hp : p s(u,v) <;> simp [tutteSign, hH, hp]
  have hm : (Polynomial.mapRingHom f).mapMatrix PG = PH := by
    dsimp [PG, PH, f]
    rw [filter_polynomialMatrix]
    congr 1
    funext i j
    exact (hs _ _).symm
  have hmd : Polynomial.map f PG.det = PH.det := by
    change Polynomial.mapRingHom f _ = _
    rw [(Polynomial.mapRingHom f).map_det, hm]
  have hgmap : (toRat (E := Sym2 V)).mapMatrix PG = (weightedTutte G w).submatrix row col :=
    mapped_polynomialMatrix_tutte G w row col
  have hhmap : (toRat (E := Sym2 V)).mapMatrix PH = (weightedTutte H w).submatrix row col :=
    mapped_polynomialMatrix_tutte H w row col
  have hpr : PH.det ≠ 0 := by
    intro hz
    rw [← hhmap, ← (toRat (E := Sym2 V)).map_det, hz, map_zero] at hn
    exact hn rfl
  have hpg : PG.det ≠ 0 := by
    intro hz
    rw [hz, Polynomial.map_zero] at hmd
    exact hpr hmd.symm
  rw [← hgmap, ← hhmap, ← (toRat (E := Sym2 V)).map_det,
    ← (toRat (E := Sym2 V)).map_det]
  constructor
  · exact (map_ne_zero_iff _ toRat_injective).mpr hpg
  · rw [toRat_degree, toRat_degree]
    have hd : PH.det.natDegree ≤ PG.det.natDegree := by
      rw [← hmd]
      exact Polynomial.natDegree_map_le
    exact_mod_cast hd

end RobustMatching.R7WeightedPhaseAlgebraLower
#print axioms RobustMatching.R7WeightedPhaseAlgebraLower.tutte_minor_restriction
