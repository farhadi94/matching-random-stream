import RobustMatching.R7AlgebraInterpretationUpper
import RobustMatching.R7AlgebraTutteEnvelope
import Mathlib.Logic.Equiv.Fintype

/-!
Actual index conversion between arbitrary nonsingular column tuples in
[A | I] and fixed-complement completed minors.
-/
noncomputable section
open scoped BigOperators
open Equiv Finset

namespace RobustMatching.R7AlgebraInterpretation
open RobustMatching.R7Algebra RobustMatching.R7AlgebraTutte
set_option backward.isDefEq.respectTransparency false
variable {V R K : Type*} [Fintype V] [DecidableEq V] [CommRing R]

def augment (A : Matrix V V R) : Matrix V (V ⊕ V) R :=
  fun i j => Sum.elim (A i) ((1 : Matrix V V R) i) j

theorem det_completed_permuted (I : Finset V) (A : Matrix V V R) (ρ : Equiv.Perm V) :
    ((completedMatrix I A ρ).submatrix id ρ).det =
      (firstExchange (A.submatrix id ρ) I).det := by
  have hm : (completedMatrix I A ρ).submatrix id ρ =
      (firstExchange ((A.submatrix id ρ).transpose) I).transpose := by
    ext i j
    by_cases hi : i ∈ I <;>
      simp [completedMatrix,firstExchange,Matrix.transpose_apply,
        Matrix.submatrix_apply,Matrix.one_apply,hi,eq_comm]
  rw [hm,Matrix.det_transpose,det_identity_padding,det_identity_padding]
  exact Matrix.det_transpose _

/-- Repeated column labels would give equal columns and a zero determinant. -/
theorem column_tuple_injective (A : Matrix V V R) (b : V → V ⊕ V)
    (hn : ((augment A).submatrix id b).det ≠ 0) : Function.Injective b := by
  intro i j hij
  by_contra hne
  exact hn (Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply,hij]))

/-- A surviving Leibniz term aligns every selected identity column with its
actual vertex. The remaining original labels extend to a permutation. -/
theorem column_tuple_normal_form [IsDomain R] (A : Matrix V V R) (b : V → V ⊕ V)
    (hn : ((augment A).submatrix id b).det ≠ 0) :
    ∃ (τ ρ : Equiv.Perm V) (I : Finset V),
      (((augment A).submatrix id b).submatrix id τ) =
        firstExchange (A.submatrix id ρ) I ∧
      (∀ i ∈ I, ∃ j, b j = Sum.inl (ρ i)) := by
  classical
  have hdet := hn
  rw [Matrix.det_apply'] at hdet
  obtain ⟨σ,_,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hp : (∏ i, ((augment A).submatrix id b) (σ i) i) ≠ 0 :=
    (mul_ne_zero_iff.mp hs).2
  have he (j : V) : (augment A) (σ j) (b j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hp j (Finset.mem_univ j)
  let b' : V → V ⊕ V := fun i => b (σ.symm i)
  have hb'inj : Function.Injective b' := (column_tuple_injective A b hn).comp σ.symm.injective
  have hid (i v : V) (hb : b' i = Sum.inr v) : i = v := by
    have hh := he (σ.symm i)
    have hh' : augment A i (b' i) ≠ 0 := by simpa [b'] using hh
    by_contra hne
    exact hh' (by simp [augment,hb,Matrix.one_apply,hne])
  let I : Finset V := Finset.univ.filter (fun i => ∃ v, b' i = Sum.inl v)
  let c : V → V := fun i => Sum.elim id id (b' i)
  have hleft (i : V) (hi : i ∈ I) : b' i = Sum.inl (c i) := by
    obtain ⟨_,v,hv⟩ := Finset.mem_filter.mp hi
    simp [c,hv]
  have hright (i : V) (hi : i ∉ I) : b' i = Sum.inr i := by
    cases hh : b' i with
    | inl v => exact (hi (by simp [I,hh])).elim
    | inr v => simpa [hid i v hh] using hh
  have hcinj : Function.Injective (fun i : {i // i ∈ I} => c i) := by
    intro i j hij
    apply Subtype.ext
    apply hb'inj
    rw [hleft i i.property,hleft j j.property]
    exact congrArg Sum.inl hij
  obtain ⟨ρ,hρ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : {i // i ∈ I} => (i : V)) (fun i : {i // i ∈ I} => c i)
    Subtype.val_injective hcinj
  refine ⟨σ.symm,ρ,I,?_,?_⟩
  · ext i j
    by_cases hj : j ∈ I
    · have hh : b (σ.symm j) = Sum.inl (ρ j) := by
        change b' j = Sum.inl (ρ j)
        rw [hρ ⟨j,hj⟩]
        exact hleft j hj
      simp [Matrix.submatrix_apply,firstExchange,hj,hh,augment,id_eq]
    · have hh : b (σ.symm j) = Sum.inr j := hright j hj
      simp [Matrix.submatrix_apply,firstExchange,hj,hh,augment,id_eq]
      rfl
  · intro i hi
    refine ⟨σ.symm i,?_⟩
    change b' i = Sum.inl (ρ i)
    rw [hρ ⟨i,hi⟩]
    exact hleft i hi

section RationalFunctions
variable [Field K]

theorem completed_firstExchange_degree (I : Finset V) (A : Matrix V V (RatFunc K))
    (ρ : Equiv.Perm V) :
    (completedMatrix I A ρ).det.intDegree =
      (firstExchange (A.submatrix id ρ) I).det.intDegree := by
  rw [← intDegree_det_permute (completedMatrix I A ρ) ρ,det_completed_permuted]

theorem completed_firstExchange_nonzero (I : Finset V) (A : Matrix V V (RatFunc K))
    (ρ : Equiv.Perm V) :
    (completedMatrix I A ρ).det ≠ 0 ↔
      (firstExchange (A.submatrix id ρ) I).det ≠ 0 := by
  rw [← det_completed_permuted I A ρ]
  constructor
  · exact det_permute_ne_zero _ _
  · intro hn hz
    apply hn
    rw [Matrix.det_permute',hz,mul_zero]

theorem completed_principal_minor_degree (I : Finset V) (A : Matrix V V (RatFunc K))
    (ρ : Equiv.Perm V) :
    (completedMatrix I A ρ).det.intDegree =
      (A.submatrix (fun i : {x // x ∈ I} => i.val)
        (fun i : {x // x ∈ I} => ρ i.val)).det.intDegree := by
  rw [completed_firstExchange_degree,det_identity_padding]
  rfl

theorem completed_principal_minor_nonzero (I : Finset V) (A : Matrix V V (RatFunc K))
    (ρ : Equiv.Perm V) :
    (completedMatrix I A ρ).det ≠ 0 ↔
      (A.submatrix (fun i : {x // x ∈ I} => i.val)
        (fun i : {x // x ∈ I} => ρ i.val)).det ≠ 0 := by
  rw [completed_firstExchange_nonzero,det_identity_padding]
  rfl

/-- Every actual nonsingular tuple has a completed minor with equal degree,
using only original column labels present in the tuple. -/
theorem column_tuple_completed_minor (A : Matrix V V (RatFunc K)) (b : V → V ⊕ V)
    (hn : ((augment A).submatrix id b).det ≠ 0) :
    ∃ (ρ : Equiv.Perm V) (I : Finset V),
      (completedMatrix I A ρ).det ≠ 0 ∧
      (completedMatrix I A ρ).det.intDegree = ((augment A).submatrix id b).det.intDegree ∧
      (∀ i ∈ I, ∃ j, b j = Sum.inl (ρ i)) := by
  obtain ⟨τ,ρ,I,hm,hcols⟩ := column_tuple_normal_form A b hn
  refine ⟨ρ,I,?_,?_,hcols⟩
  · apply (completed_firstExchange_nonzero I A ρ).mpr
    rw [←hm]
    exact det_permute_ne_zero _ τ hn
  · rw [completed_firstExchange_degree,←hm,intDegree_det_permute]

def paddedColumns (I : Finset V) (ρ : Equiv.Perm V) : V → V ⊕ V :=
  fun i => if i ∈ I then Sum.inl (ρ i) else Sum.inr i

theorem paddedColumns_matrix (I : Finset V) (A : Matrix V V (RatFunc K)) (ρ : Equiv.Perm V) :
    (augment A).submatrix id (paddedColumns I ρ) = firstExchange (A.submatrix id ρ) I := by
  ext i j
  by_cases hj : j ∈ I <;>
    simp [Matrix.submatrix_apply,paddedColumns,firstExchange,augment,hj,id_eq] <;> rfl

/-- Conversely, padding any nonzero completed minor gives an actual nonsingular
column tuple in the identity-augmented matrix with the same degree. -/
theorem completed_minor_padded_tuple (I : Finset V) (A : Matrix V V (RatFunc K))
    (ρ : Equiv.Perm V) (hn : (completedMatrix I A ρ).det ≠ 0) :
    ((augment A).submatrix id (paddedColumns I ρ)).det ≠ 0 ∧
      ((augment A).submatrix id (paddedColumns I ρ)).det.intDegree =
        (completedMatrix I A ρ).det.intDegree := by
  rw [paddedColumns_matrix]
  exact ⟨(completed_firstExchange_nonzero I A ρ).mp hn,
    (completed_firstExchange_degree I A ρ).symm⟩

end RationalFunctions
end RobustMatching.R7AlgebraInterpretation
