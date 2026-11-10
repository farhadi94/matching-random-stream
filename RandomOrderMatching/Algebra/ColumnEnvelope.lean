import RandomOrderMatching.Algebra.DeterminantExchange

/-!
Submodularity of actual rational-function determinant availability envelopes.
The exchanged matrices are constructed by `matrix_multiple_exchange`;
there is no assumed valuated-matroid exchange property.
-/
noncomputable section
open scoped BigOperators
open Matrix Finset

namespace RandomOrderMatching.Algebra

variable {n E K : Type*} [Fintype n] [DecidableEq n]
  [Fintype E] [DecidableEq E] [Field K]

def columnMatrix (C : Matrix n E (RatFunc K)) (b : n → E) : Matrix n n (RatFunc K) :=
  C.submatrix id b

def columnBases (C : Matrix n E (RatFunc K)) (S : Finset E) : Finset (n → E) := by
  classical
  exact Finset.univ.filter (fun b => (columnMatrix C b).det ≠ 0 ∧ ∀ i, b i ∈ S)

theorem mem_columnBases (C : Matrix n E (RatFunc K)) (S : Finset E) (b : n → E) :
    b ∈ columnBases C S ↔ (columnMatrix C b).det ≠ 0 ∧ ∀ i, b i ∈ S := by
  classical
  simp [columnBases]

def columnEnvelope (C : Matrix n E (RatFunc K)) (S : Finset E) : ℤ := by
  classical
  exact if h : (columnBases C S).Nonempty then
    (columnBases C S).sup' h (fun b => (columnMatrix C b).det.intDegree) else 0

theorem columnEnvelope_attained (C : Matrix n E (RatFunc K)) (S : Finset E)
    (h : (columnBases C S).Nonempty) :
    ∃ b ∈ columnBases C S, (columnMatrix C b).det.intDegree = columnEnvelope C S := by
  classical
  rw [columnEnvelope, dif_pos h]
  obtain ⟨b, hb, heq⟩ := Finset.exists_mem_eq_sup' h (fun b => (columnMatrix C b).det.intDegree)
  exact ⟨b, hb, heq.symm⟩

theorem columnEnvelope_upper (C : Matrix n E (RatFunc K)) (S : Finset E)
    (b : n → E) (hb : b ∈ columnBases C S) :
    (columnMatrix C b).det.intDegree ≤ columnEnvelope C S := by
  classical
  have h : (columnBases C S).Nonempty := ⟨b, hb⟩
  rw [columnEnvelope, dif_pos h]
  exact Finset.le_sup' (fun b => (columnMatrix C b).det.intDegree) hb

/-- An always-available nonsingular column tuple ensures finite maxima. -/
theorem columnBases_nonempty (C : Matrix n E (RatFunc K)) (D S : Finset E)
    (d : n → E) (hd : (columnMatrix C d).det ≠ 0) (hD : ∀ i, d i ∈ D) :
    (columnBases C (D ∪ S)).Nonempty := by
  refine ⟨d, (mem_columnBases C (D ∪ S) d).mpr ⟨hd, ?_⟩⟩
  intro i
  exact Finset.mem_union_left _ (hD i)

theorem columnMatrix_mixed (C : Matrix n E (RatFunc K)) (a b : n → E)
    (S : Finset n) :
    columnMatrix C (S.piecewise b a) =
      mixedColumns (columnMatrix C a) (columnMatrix C b) S := by
  ext i j
  by_cases hj : j ∈ S <;> simp [columnMatrix, mixedColumns, Finset.piecewise, hj]

/-- The maximum degree of an available nonsingular column tuple is submodular.
All maxima and exchange inequalities refer to the actual matrix C. -/
theorem columnEnvelope_submodular (C : Matrix n E (RatFunc K))
    (D : Finset E) (d : n → E)
    (hd : (columnMatrix C d).det ≠ 0) (hD : ∀ i, d i ∈ D)
    (U V : Finset E) :
    columnEnvelope C (D ∪ (U ∪ V)) + columnEnvelope C (D ∪ (U ∩ V)) ≤
      columnEnvelope C (D ∪ U) + columnEnvelope C (D ∪ V) := by
  classical
  obtain ⟨a, ha, hva⟩ := columnEnvelope_attained C (D ∪ (U ∪ V))
    (columnBases_nonempty C D (U ∪ V) d hd hD)
  obtain ⟨b, hb, hvb⟩ := columnEnvelope_attained C (D ∪ (U ∩ V))
    (columnBases_nonempty C D (U ∩ V) d hd hD)
  obtain ⟨han, hau⟩ := (mem_columnBases C _ a).mp ha
  obtain ⟨hbn, hbu⟩ := (mem_columnBases C _ b).mp hb
  let S : Finset n := Finset.univ.filter (fun i => a i ∉ D ∪ U)
  obtain ⟨σ, hp, hq, hval⟩ := matrix_multiple_exchange
    (columnMatrix C a) (columnMatrix C b) S han hbn
  let bσ : n → E := fun i => b (σ i)
  let x : n → E := S.piecewise bσ a
  let y : n → E := S.piecewise a bσ
  have hσ : (columnMatrix C b).submatrix id σ = columnMatrix C bσ := rfl
  simp_rw [hσ, ← columnMatrix_mixed] at hp hq hval
  have hx : x ∈ columnBases C (D ∪ U) := by
    apply (mem_columnBases C _ x).mpr
    refine ⟨hp, ?_⟩
    intro i
    by_cases hi : i ∈ S
    · have hh := hbu (σ i)
      simp only [Finset.mem_union, Finset.mem_inter] at hh
      simpa [x, Finset.piecewise, hi, bσ] using hh.imp_right And.left
    · have hh : a i ∈ D ∪ U := by
        by_contra hn
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩)
      simpa [x, Finset.piecewise, hi] using hh
  have hy : y ∈ columnBases C (D ∪ V) := by
    apply (mem_columnBases C _ y).mpr
    refine ⟨hq, ?_⟩
    intro i
    by_cases hi : i ∈ S
    · have hn : a i ∉ D ∪ U := by simpa [S] using hi
      have hh := hau i
      have hv : a i ∈ D ∪ V := by
        simp only [Finset.mem_union] at hn hh ⊢
        tauto
      simpa [y, Finset.piecewise, hi] using hv
    · have hh := hbu (σ i)
      simp only [Finset.mem_union, Finset.mem_inter] at hh
      simpa [y, Finset.piecewise, hi, bσ] using hh.imp_right And.right
  have hxu := columnEnvelope_upper C (D ∪ U) x hx
  have hyu := columnEnvelope_upper C (D ∪ V) y hy
  rw [← hva, ← hvb]
  exact hval.trans (add_le_add hxu hyu)

end RandomOrderMatching.Algebra
