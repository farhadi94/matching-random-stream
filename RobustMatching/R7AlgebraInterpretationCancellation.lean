import RobustMatching.R7AlgebraInterpretationCycles

/-!
Actual sign-reversing involution on all odd-cycle terms of a completed minor.
No cancellation or component-selection oracle is supplied as a hypothesis.
-/
noncomputable section
open scoped BigOperators
open Equiv Finset

namespace RobustMatching.R7AlgebraInterpretation
set_option backward.isDefEq.respectTransparency false
variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]

def partialProduct (I : Finset V) (A : Matrix V V R) (π : Equiv.Perm V) : R :=
  ∏ i, if i ∈ I then A i (π i) else 1

def partialTerm (I : Finset V) (A : Matrix V V R) (π : Equiv.Perm V) : R :=
  (Equiv.Perm.sign π : ℤ) * partialProduct I A π

theorem reverseCycle_apply_successor (π c : Equiv.Perm V)
    (hc : c ∈ π.cycleFactorsFinset) {v : V} (hv : v ∈ c.support) :
    reverseCycle π c (c v) = v := by
  have hv' : c⁻¹ v ∈ c.support := by
    simpa only [Equiv.Perm.support_inv] using
      (Equiv.Perm.apply_mem_support (f := c⁻¹)).mpr (by simpa using hv)
  have he := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 (c⁻¹ v) hv'
  simpa [reverseCycle, Equiv.Perm.mul_apply] using he.symm

theorem partialProduct_reverseCycle (I : Finset V) (A : Matrix V V R)
    (hskew : ∀ i j, A i j = - A j i) (π c : Equiv.Perm V)
    (hc : c ∈ π.cycleFactorsFinset) (hI : c.support ⊆ I) :
    partialProduct I A (reverseCycle π c) =
      (-1 : R)^c.support.card * partialProduct I A π := by
  classical
  have hpoint (i : V) :
      (if c i ∈ I then A (c i) (reverseCycle π c (c i)) else 1) =
      (if i ∈ c.support then (-1 : R) else 1) *
        (if i ∈ I then A i (π i) else 1) := by
    by_cases hi : i ∈ c.support
    · have hci := Equiv.Perm.apply_mem_support.mpr hi
      have he := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 i hi
      simp only [if_pos (hI hi), if_pos (hI hci), if_pos hi,
        reverseCycle_apply_successor π c hc hi]
      rw [← he, hskew]
      ring
    · have he : c i = i := Equiv.Perm.notMem_support.mp hi
      simp only [he, reverseCycle_outside π c hi, if_neg hi, one_mul]
  unfold partialProduct
  rw [← Equiv.prod_comp c (fun i => if i ∈ I then A i (reverseCycle π c i) else 1)]
  simp_rw [hpoint]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

theorem sign_reverseCycle (π c : Equiv.Perm V) :
    Equiv.Perm.sign (reverseCycle π c) = Equiv.Perm.sign π := by
  unfold reverseCycle
  simp only [map_mul, Equiv.Perm.sign_inv]
  rcases Int.units_eq_one_or (Equiv.Perm.sign c) with h | h <;> simp [h]

theorem partialTerm_reverseCycle_odd (I : Finset V) (A : Matrix V V R)
    (hskew : ∀ i j, A i j = - A j i) (π c : Equiv.Perm V)
    (hc : c ∈ π.cycleFactorsFinset) (hI : c.support ⊆ I) (ho : Odd c.support.card) :
    partialTerm I A (reverseCycle π c) = - partialTerm I A π := by
  unfold partialTerm
  rw [sign_reverseCycle, partialProduct_reverseCycle I A hskew π c hc hI, ho.neg_one_pow]
  ring

def completionPerms (I : Finset V) (ρ : Equiv.Perm V) : Finset (Equiv.Perm V) := by
  classical
  exact Finset.univ.filter (fun π => ∀ v ∉ I, π v = ρ v)

theorem mem_completionPerms (I : Finset V) (ρ π : Equiv.Perm V) :
    π ∈ completionPerms I ρ ↔ ∀ v ∉ I, π v = ρ v := by
  classical
  simp [completionPerms]

def completedMatrix (I : Finset V) (A : Matrix V V R) (ρ : Equiv.Perm V) : Matrix V V R :=
  fun i j => if i ∈ I then A i j else if ρ i = j then 1 else 0

/-- This actual full determinant is the fixed-complement completion of a minor. -/
theorem det_completedMatrix (I : Finset V) (A : Matrix V V R) (ρ : Equiv.Perm V) :
    (completedMatrix I A ρ).det = ∑ π ∈ completionPerms I ρ, partialTerm I A π := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply']
  unfold completionPerms
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hh : ∀ v ∉ I, π v = ρ v
  · rw [if_pos hh]
    unfold partialTerm partialProduct
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ I
    · simp [completedMatrix, Matrix.transpose_apply, hi]
    · simp [completedMatrix, Matrix.transpose_apply, hi, hh i hi]
  · rw [if_neg hh]
    push Not at hh
    obtain ⟨i,hi,hne⟩ := hh
    have hz : (completedMatrix I A ρ).transpose (π i) i = 0 := by
      simp [completedMatrix, Matrix.transpose_apply, hi, Ne.symm hne]
    have hp : (∏ j, (completedMatrix I A ρ).transpose (π j) j) = 0 :=
      Finset.prod_eq_zero (f := fun j => (completedMatrix I A ρ).transpose (π j) j)
        (Finset.mem_univ i) hz
    rw [hp, mul_zero]

section GlobalCancellation
variable [LinearOrder V] [IsDomain R] [CharZero R]

theorem partialTerm_reverseBad (I : Finset V) (A : Matrix V V R)
    (hskew : ∀ i j, A i j = - A j i) (π : Equiv.Perm V)
    (h : (badVertices I π).Nonempty) :
    partialTerm I A (reverseBad I π) = -partialTerm I A π := by
  classical
  rw [reverseBad, dif_pos h]
  have hs := chosenCycle_spec I π h
  exact partialTerm_reverseCycle_odd I A hskew π _ hs.1 hs.2.1 hs.2.2.1

/-- Complete cancellation of all terms with an internal odd cycle. -/
theorem sum_bad_completion_terms_eq_zero (I : Finset V) (A : Matrix V V R)
    (hskew : ∀ i j, A i j = - A j i) (ρ : Equiv.Perm V) :
    (∑ π ∈ (completionPerms I ρ).filter (fun π => (badVertices I π).Nonempty),
      partialTerm I A π) = 0 := by
  classical
  let S := (completionPerms I ρ).filter (fun π => (badVertices I π).Nonempty)
  have hmem (π : Equiv.Perm V) (hπ : π ∈ S) : reverseBad I π ∈ S := by
    obtain ⟨hc,hb⟩ := Finset.mem_filter.mp hπ
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_completionPerms I ρ _).mpr
      intro v hv
      rw [reverseBad_outside I π hv]
      exact (mem_completionPerms I ρ π).mp hc v hv
    · rwa [badVertices_reverseBad]
  apply Finset.sum_involution (fun π (_ : π ∈ S) => reverseBad I π)
  · intro π hπ
    rw [partialTerm_reverseBad I A hskew π (Finset.mem_filter.mp hπ).2, add_neg_cancel]
  · intro π hπ hn heq
    have hh := partialTerm_reverseBad I A hskew π (Finset.mem_filter.mp hπ).2
    rw [heq] at hh
    exact hn (CharZero.eq_neg_self_iff.mp hh)
  · exact hmem
  · intro π _
    exact reverseBad_involution I π

/-- Only even-cycle terms are needed in the determinant of any completed minor. -/
theorem det_completedMatrix_without_odd_cycles (I : Finset V) (A : Matrix V V R)
    (hskew : ∀ i j, A i j = - A j i) (ρ : Equiv.Perm V) :
    (completedMatrix I A ρ).det =
      ∑ π ∈ (completionPerms I ρ).filter (fun π => ¬ (badVertices I π).Nonempty),
        partialTerm I A π := by
  classical
  rw [det_completedMatrix]
  have hh := Finset.sum_filter_add_sum_filter_not (s := completionPerms I ρ)
    (p := fun π => (badVertices I π).Nonempty) (f := partialTerm I A)
  rw [sum_bad_completion_terms_eq_zero I A hskew ρ, zero_add] at hh
  exact hh.symm

end GlobalCancellation
end RobustMatching.R7AlgebraInterpretation
