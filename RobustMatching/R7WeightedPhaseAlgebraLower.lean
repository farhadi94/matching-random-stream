import RobustMatching.R7AlgebraTutteEnvelope
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.BigOperators

/-! Generic weighted bipartite determinant lower bound by specialization.
No leading-term or noncancellation hypothesis is used. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7WeightedPhaseAlgebraLower
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
abbrev Coeff (E : Type*) := MvPolynomial E ℚ
abbrev CoeffField (E : Type*) := FractionRing (Coeff E)

def polynomialMatrix (edge : ι → ι → E) (a : ι → ι → ℚ) (w : ι → ι → ℕ) :
    Matrix ι ι (Polynomial (Coeff E)) := fun i j =>
  Polynomial.C (MvPolynomial.C (a i j) * MvPolynomial.X (edge i j)) *
    Polynomial.X ^ w i j

def diagonalSpecialization (edge : ι → ι → E) : Coeff E →+* ℚ := by
  classical
  exact MvPolynomial.eval₂Hom (RingHom.id ℚ)
    (fun e => if ∃ i, e = edge i i then 1 else 0)

theorem specialize_diagonal (edge : ι → ι → E)
    (hsep : ∀ i j k, edge i j = edge k k → i = j)
    (a : ι → ι → ℚ) (w : ι → ι → ℕ) :
    (Polynomial.mapRingHom (diagonalSpecialization edge)).mapMatrix
      (polynomialMatrix edge a w) =
    Matrix.diagonal (fun i => Polynomial.C (a i i) * Polynomial.X ^ w i i) := by
  classical
  funext i j
  by_cases hij : i = j
  · subst j
    have hx : ∃ k, edge i i = edge k k := ⟨i, rfl⟩
    simp [polynomialMatrix, diagonalSpecialization, hx]
  · have hx : ¬ ∃ k, edge i j = edge k k := by
      rintro ⟨k, hk⟩
      exact hij (hsep i j k hk)
    simp [polynomialMatrix, diagonalSpecialization, hij, hx]

theorem polynomial_det_matching_lower (edge : ι → ι → E)
    (hsep : ∀ i j k, edge i j = edge k k → i = j)
    (a : ι → ι → ℚ) (ha : ∀ i, a i i ≠ 0) (w : ι → ι → ℕ) :
    (polynomialMatrix edge a w).det ≠ 0 ∧
    (∑ i, w i i) ≤ (polynomialMatrix edge a w).det.natDegree := by
  classical
  let f := diagonalSpecialization edge
  have hm : Polynomial.map f (polynomialMatrix edge a w).det =
      ∏ i, (Polynomial.C (a i i) * Polynomial.X ^ w i i : Polynomial ℚ) := by
    change Polynomial.mapRingHom f _ = _
    rw [(Polynomial.mapRingHom f).map_det]
    rw [specialize_diagonal edge hsep a w, Matrix.det_diagonal]
  have hfactor : ∀ i, (Polynomial.C (a i i) * Polynomial.X ^ w i i : Polynomial ℚ) ≠ 0 := by
    intro i
    exact mul_ne_zero (by simpa using ha i) (pow_ne_zero _ Polynomial.X_ne_zero)
  have hp : (∏ i, (Polynomial.C (a i i) * Polynomial.X ^ w i i : Polynomial ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hfactor i)
  constructor
  · intro hz
    rw [hz, Polynomial.map_zero] at hm
    exact hp hm.symm
  · have hd : (Polynomial.map f (polynomialMatrix edge a w).det).natDegree = ∑ i, w i i := by
      rw [hm, Polynomial.natDegree_prod Finset.univ _ (fun i _ => hfactor i)]
      simp only [Polynomial.natDegree_C_mul_X_pow _ _ (ha _)]
    rw [← hd]
    exact Polynomial.natDegree_map_le

def toRat : Polynomial (Coeff E) →+* RatFunc (CoeffField E) :=
  (algebraMap (Polynomial (CoeffField E)) (RatFunc (CoeffField E))).comp
    (Polynomial.mapRingHom (algebraMap (Coeff E) (CoeffField E)))

theorem toRat_injective : Function.Injective (toRat : Polynomial (Coeff E) →+* _) := by
  exact (RatFunc.algebraMap_injective (CoeffField E)).comp
    (Polynomial.map_injective _ (IsFractionRing.injective (Coeff E) (CoeffField E)))

theorem toRat_degree (p : Polynomial (Coeff E)) :
    (toRat p).intDegree = p.natDegree := by
  unfold toRat
  rw [RingHom.comp_apply, RatFunc.intDegree_polynomial]
  exact_mod_cast Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective (Coeff E) (CoeffField E)) p

theorem rational_det_matching_lower (edge : ι → ι → E)
    (hsep : ∀ i j k, edge i j = edge k k → i = j)
    (a : ι → ι → ℚ) (ha : ∀ i, a i i ≠ 0) (w : ι → ι → ℕ) :
    ((toRat (E := E)).mapMatrix (polynomialMatrix edge a w)).det ≠ 0 ∧
    (∑ i, (w i i : ℤ)) ≤
      ((toRat (E := E)).mapMatrix (polynomialMatrix edge a w)).det.intDegree := by
  obtain ⟨hn, hd⟩ := polynomial_det_matching_lower edge hsep a ha w
  rw [← (toRat (E := E)).map_det]
  constructor
  · exact (map_ne_zero_iff _ toRat_injective).mpr hn
  · rw [toRat_degree]
    exact_mod_cast hd

end RobustMatching.R7WeightedPhaseAlgebraLower
#print axioms RobustMatching.R7WeightedPhaseAlgebraLower.rational_det_matching_lower
