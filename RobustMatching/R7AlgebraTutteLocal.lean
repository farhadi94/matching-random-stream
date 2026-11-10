import RobustMatching.R7AlgebraLaplace
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
Local identities for the ordinary commutative, shared-edge-variable Tutte
matrix. These are not a claimed proof of its full marked-path interpretation.
-/
noncomputable section
open scoped BigOperators

namespace RobustMatching.R7AlgebraTutte

section LocalCancellation
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def signedTerm (A : Matrix ι ι R) (σ : Equiv.Perm ι) : R :=
  (Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i

/-- Reversing all arcs on a directed component changes its term by its parity.
Applied to the vertex type of one cycle, this is the local cancellation identity. -/
theorem reverse_term (A : Matrix ι ι R)
    (hskew : ∀ i j, A i j = - A j i) (σ : Equiv.Perm ι) :
    signedTerm A σ.symm = (-1 : R) ^ Fintype.card ι * signedTerm A σ := by
  have hp : (∏ i, A (σ.symm i) i) = ∏ i, A i (σ i) := by
    simpa using (Equiv.prod_comp σ (fun i => A (σ.symm i) i)).symm
  unfold signedTerm
  rw [Equiv.Perm.sign_symm, hp]
  have hn : (∏ i, A i (σ i)) = (-1 : R) ^ Fintype.card ι * ∏ i, A (σ i) i := by
    simp_rw [hskew _ (σ _)]
    rw [Finset.prod_neg, Finset.card_univ]
  rw [hn]
  ring

theorem odd_reverse_cancels (A : Matrix ι ι R)
    (hskew : ∀ i j, A i j = - A j i) (σ : Equiv.Perm ι)
    (hodd : Odd (Fintype.card ι)) : signedTerm A σ + signedTerm A σ.symm = 0 := by
  rw [reverse_term A hskew σ, hodd.neg_one_pow]
  ring

theorem even_reverse_agrees (A : Matrix ι ι R)
    (hskew : ∀ i j, A i j = - A j i) (σ : Equiv.Perm ι)
    (heven : Even (Fintype.card ι)) : signedTerm A σ.symm = signedTerm A σ := by
  rw [reverse_term A hskew σ, heven.neg_one_pow, one_mul]

/-- A common matching edge gives a square, not two independent variables. -/
theorem doubled_edge_det (z : R) :
    Matrix.det (!![0,z; -z,0] : Matrix (Fin 2) (Fin 2) R) = z^2 := by
  simp [Matrix.det_fin_two, pow_two]

end LocalCancellation

section WeightedMatrix
variable {V : Type*} [Fintype V] [LinearOrder V]

abbrev EdgeField (V : Type*) := FractionRing (MvPolynomial (Sym2 V) ℚ)

/-- One algebraically independent variable for each unordered original edge. -/
def edgeVariable (e : Sym2 V) : EdgeField V :=
  algebraMap (MvPolynomial (Sym2 V) ℚ) (EdgeField V) (MvPolynomial.X e)

theorem edgeVariable_ne_zero (e : Sym2 V) : edgeVariable e ≠ 0 := by
  unfold edgeVariable
  intro h
  exact MvPolynomial.X_ne_zero e (IsFractionRing.to_map_eq_zero_iff.mp h)

def weightedVariable (w : Sym2 V → ℕ) (e : Sym2 V) : RatFunc (EdgeField V) :=
  RatFunc.C (edgeVariable e) * RatFunc.X ^ w e

theorem weightedVariable_ne_zero (w : Sym2 V → ℕ) (e : Sym2 V) :
    weightedVariable w e ≠ 0 := by
  exact mul_ne_zero ((map_ne_zero RatFunc.C).mpr (edgeVariable_ne_zero e))
    (pow_ne_zero _ RatFunc.X_ne_zero)

theorem intDegree_pow_X (m : ℕ) :
    (RatFunc.X ^ m : RatFunc (EdgeField V)).intDegree = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ RatFunc.X_ne_zero) RatFunc.X_ne_zero,
      ih, RatFunc.intDegree_X]
    simp

theorem weightedVariable_degree (w : Sym2 V → ℕ) (e : Sym2 V) :
    (weightedVariable w e).intDegree = w e := by
  unfold weightedVariable
  rw [RatFunc.intDegree_mul ((map_ne_zero RatFunc.C).mpr (edgeVariable_ne_zero e))
      (pow_ne_zero _ RatFunc.X_ne_zero), RatFunc.intDegree_C, intDegree_pow_X, zero_add]

/-- Ordinary skew Tutte matrix, with the same variable used in both orientations. -/
def weightedTutte (G : SimpleGraph V) (w : Sym2 V → ℕ) :
    Matrix V V (RatFunc (EdgeField V)) := by
  classical
  exact fun i j => if G.Adj i j then
    if i < j then weightedVariable w s(i,j) else -weightedVariable w s(j,i)
    else 0

theorem weightedTutte_skew (G : SimpleGraph V) (w : Sym2 V → ℕ) (i j : V) :
    weightedTutte G w i j = -weightedTutte G w j i := by
  classical
  by_cases ha : G.Adj i j
  · have hb := ha.symm
    have hn := G.ne_of_adj ha
    rcases lt_or_gt_of_ne hn with hij | hji
    · simp [weightedTutte, ha, hb, hij, not_lt_of_gt hij]
    · simp [weightedTutte, ha, hb, hji, not_lt_of_gt hji]
  · have hb : ¬ G.Adj j i := fun h => ha h.symm
    simp [weightedTutte, ha, hb]

theorem weightedTutte_diag (G : SimpleGraph V) (w : Sym2 V → ℕ) (i : V) :
    weightedTutte G w i i = 0 := by
  classical
  simp [weightedTutte]

theorem doubled_weighted_edge_degree (w : Sym2 V → ℕ) (e : Sym2 V) :
    (Matrix.det (!![0,weightedVariable w e; -weightedVariable w e,0] :
      Matrix (Fin 2) (Fin 2) (RatFunc (EdgeField V)))).intDegree = 2 * w e := by
  rw [doubled_edge_det, pow_two,
    RatFunc.intDegree_mul (weightedVariable_ne_zero w e) (weightedVariable_ne_zero w e),
    weightedVariable_degree]
  ring

end WeightedMatrix
end RobustMatching.R7AlgebraTutte
