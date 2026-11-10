import RandomOrderMatching.Algebra.ColumnEnvelope
import RandomOrderMatching.Algebra.Tutte.Matrix

/-!
Actual identity-augmented weighted Tutte matrix with arbitrary original-column
availability. Submodularity here is unconditional for this concrete matrix.
Identifying its value with the graph-defined marked-path value remains separate.
-/
noncomputable section
open scoped BigOperators

namespace RandomOrderMatching.Algebra.Tutte
open RandomOrderMatching.Algebra
set_option backward.isDefEq.respectTransparency false

/-- Padding a principal minor with identity columns changes no determinant.
Applying this to a column-permuted matrix gives arbitrary equally-sized
row/column minors once their indexing bijection is supplied. -/
theorem det_identity_padding {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) (S : Finset n) :
    (firstExchange A S).det =
      (A.submatrix (fun i : {x // x ∈ S} => i.val) (fun i : {x // x ∈ S} => i.val)).det := by
  classical
  let e := Equiv.sumCompl (fun x : n => x ∈ S)
  let P : Matrix {x // x ∈ S} {x // x ∈ S} R := A.submatrix Subtype.val Subtype.val
  let L : Matrix {x // x ∉ S} {x // x ∈ S} R := A.submatrix Subtype.val Subtype.val
  have ha : (firstExchange A S).submatrix e e = Matrix.fromBlocks P 0 L 1 := by
    ext (i | i) (j | j)
    · simp [firstExchange, e, P, j.prop]
    · have hne : (i : n) ≠ (j : n) := fun h => j.prop (h ▸ i.prop)
      simp [firstExchange, e, j.prop, Matrix.one_apply, hne]
    · simp [firstExchange, e, L, j.prop]
    · simp +instances only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inr,
        firstExchange, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Subtype.ext_iff]
      rw [if_neg j.prop]
  rw [← Matrix.det_submatrix_equiv_self e (firstExchange A S), ha]
  simp [Matrix.det_fromBlocks_zero₂₁, P]

variable {V : Type*} [Fintype V] [LinearOrder V]

def augmentedTutte (G : SimpleGraph V) (w : Sym2 V → ℕ) :
    Matrix V (V ⊕ V) (RatFunc (EdgeField V)) :=
  fun i j => Sum.elim (weightedTutte G w i) ((1 : Matrix V V _) i) j

def identityColumns : Finset (V ⊕ V) := Finset.univ.image Sum.inr

def originalColumns (S : Finset V) : Finset (V ⊕ V) := S.image Sum.inl

theorem identity_basis (G : SimpleGraph V) (w : Sym2 V → ℕ) :
    columnMatrix (augmentedTutte G w) Sum.inr = 1 := by
  rfl

theorem originalColumns_union (S T : Finset V) :
    originalColumns (S ∪ T) = originalColumns S ∪ originalColumns T := by
  exact Finset.image_union S T

theorem originalColumns_inter (S T : Finset V) :
    originalColumns (S ∩ T) = originalColumns S ∩ originalColumns T := by
  ext (i | i) <;> simp [originalColumns]

def availableTutteValue (G : SimpleGraph V) (w : Sym2 V → ℕ) (S : Finset V) : ℤ :=
  columnEnvelope (augmentedTutte G w) (identityColumns ∪ originalColumns S)

theorem availableTutteValue_submodular (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (S T : Finset V) :
    availableTutteValue G w (S ∪ T) + availableTutteValue G w (S ∩ T) ≤
      availableTutteValue G w S + availableTutteValue G w T := by
  have hn : (columnMatrix (augmentedTutte G w) Sum.inr).det ≠ 0 := by
    rw [identity_basis, Matrix.det_one]
    exact one_ne_zero
  have hi : ∀ i : V, Sum.inr i ∈ (identityColumns : Finset (V ⊕ V)) := by
    intro i
    simp [identityColumns]
  have hh := columnEnvelope_submodular (augmentedTutte G w) identityColumns Sum.inr
    hn hi (originalColumns S) (originalColumns T)
  simpa only [availableTutteValue, originalColumns_union, originalColumns_inter] using hh

def markedTutteValue (G : SimpleGraph V) (w : Sym2 V → ℕ) (M : Finset V) : ℤ :=
  availableTutteValue G w (Finset.univ \ M)

theorem markedTutteValue_submodular (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (S T : Finset V) :
    markedTutteValue G w (S ∪ T) + markedTutteValue G w (S ∩ T) ≤
      markedTutteValue G w S + markedTutteValue G w T := by
  have hh := availableTutteValue_submodular G w (Finset.univ \ S) (Finset.univ \ T)
  have hu : (Finset.univ \ S) ∪ (Finset.univ \ T) = Finset.univ \ (S ∩ T) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and]
    tauto
  have hi : (Finset.univ \ S) ∩ (Finset.univ \ T) = Finset.univ \ (S ∪ T) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and]
    tauto
  rw [hu,hi] at hh
  unfold markedTutteValue
  linarith

end RandomOrderMatching.Algebra.Tutte
