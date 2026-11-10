import RandomOrderMatching.Algebra.Tutte.Matrix
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
Global cycle reversal for partial-permutation determinant terms.
-/
noncomputable section
open scoped BigOperators
open Equiv Finset

namespace RandomOrderMatching.Algebra.Tutte.Representation
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V]

def reverseCycle (π c : Equiv.Perm V) : Equiv.Perm V := (π * c⁻¹) * c⁻¹

theorem reverseCycle_twice (π c : Equiv.Perm V) :
    reverseCycle (reverseCycle π c) c⁻¹ = π := by
  simp [reverseCycle, mul_assoc]

theorem reverseCycle_outside (π c : Equiv.Perm V) {v : V}
    (hv : v ∉ c.support) : reverseCycle π c v = π v := by
  have hi : c⁻¹ v = v := (Equiv.Perm.notMem_support.mp (by simpa using hv))
  simp [reverseCycle, Equiv.Perm.mul_apply, hi]

theorem reverseCycle_factors (π c : Equiv.Perm V) (hc : c ∈ π.cycleFactorsFinset) :
    (reverseCycle π c).cycleFactorsFinset =
      (π*c⁻¹).cycleFactorsFinset ∪ {c⁻¹} := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  rw [reverseCycle, hd.inv_right.cycleFactorsFinset_mul_eq_union,
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.inv.cycleFactorsFinset_eq_singleton]

theorem originalCycle_factors (π c : Equiv.Perm V) (hc : c ∈ π.cycleFactorsFinset) :
    π.cycleFactorsFinset = (π*c⁻¹).cycleFactorsFinset ∪ {c} := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hp : (π*c⁻¹)*c = π := by simp [mul_assoc]
  calc
    π.cycleFactorsFinset = ((π*c⁻¹)*c).cycleFactorsFinset := congrArg _ hp.symm
    _ = _ := by rw [hd.cycleFactorsFinset_mul_eq_union,
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.cycleFactorsFinset_eq_singleton]

theorem inverse_mem_reverseCycle (π c : Equiv.Perm V) (hc : c ∈ π.cycleFactorsFinset) :
    c⁻¹ ∈ (reverseCycle π c).cycleFactorsFinset := by
  rw [reverseCycle_factors π c hc]
  simp

def badVertices (I : Finset V) (π : Equiv.Perm V) : Finset V := by
  classical
  exact π.cycleFactorsFinset.biUnion fun c =>
    if c.support ⊆ I ∧ Odd c.support.card then c.support else ∅

theorem badVertices_factorization (I : Finset V) (π c : Equiv.Perm V)
    (hc : c ∈ π.cycleFactorsFinset) :
    badVertices I π = badVertices I (π*c⁻¹) ∪
      (if c.support ⊆ I ∧ Odd c.support.card then c.support else ∅) := by
  classical
  unfold badVertices
  rw [originalCycle_factors π c hc, Finset.union_biUnion, Finset.singleton_biUnion]

/-- The set used to select a cycle is invariant under reversal, because it
depends on cycle supports and parity rather than on orientation. -/
theorem badVertices_reverseCycle (I : Finset V) (π c : Equiv.Perm V)
    (hc : c ∈ π.cycleFactorsFinset) :
    badVertices I (reverseCycle π c) = badVertices I π := by
  classical
  rw [badVertices_factorization I π c hc]
  unfold badVertices
  rw [reverseCycle_factors π c hc, Finset.union_biUnion, Finset.singleton_biUnion]
  simp

theorem mem_badVertices (I : Finset V) (π : Equiv.Perm V) (v : V) :
    v ∈ badVertices I π ↔ ∃ c ∈ π.cycleFactorsFinset,
      c.support ⊆ I ∧ Odd c.support.card ∧ v ∈ c.support := by
  classical
  simp only [badVertices, Finset.mem_biUnion]
  constructor
  · rintro ⟨c,hc,hv⟩
    split_ifs at hv with hh
    · exact ⟨c,hc,hh.1,hh.2,hv⟩
    · simp at hv
  · rintro ⟨c,hc,hI,ho,hv⟩
    exact ⟨c,hc,by simp [hI,ho,hv]⟩

section Chosen
variable [LinearOrder V]

def chosenVertex (I : Finset V) (π : Equiv.Perm V)
    (h : (badVertices I π).Nonempty) : V := (badVertices I π).min' h

def chosenCycle (I : Finset V) (π : Equiv.Perm V)
    (h : (badVertices I π).Nonempty) : Equiv.Perm V := π.cycleOf (chosenVertex I π h)

theorem chosenCycle_spec (I : Finset V) (π : Equiv.Perm V)
    (h : (badVertices I π).Nonempty) :
    chosenCycle I π h ∈ π.cycleFactorsFinset ∧
      (chosenCycle I π h).support ⊆ I ∧ Odd (chosenCycle I π h).support.card ∧
      chosenVertex I π h ∈ (chosenCycle I π h).support := by
  classical
  have hv : chosenVertex I π h ∈ badVertices I π := Finset.min'_mem _ h
  obtain ⟨c,hc,hI,ho,hv⟩ := (mem_badVertices I π _).mp hv
  have he : c = chosenCycle I π h := Equiv.Perm.cycle_is_cycleOf hv hc
  simpa [← he] using And.intro hc (And.intro hI (And.intro ho hv))

theorem chosenCycle_reverse (I : Finset V) (π : Equiv.Perm V)
    (h : (badVertices I π).Nonempty)
    (h' : (badVertices I (reverseCycle π (chosenCycle I π h))).Nonempty) :
    chosenCycle I (reverseCycle π (chosenCycle I π h)) h' = (chosenCycle I π h)⁻¹ := by
  classical
  let c := chosenCycle I π h
  have hs := chosenCycle_spec I π h
  have hb := badVertices_reverseCycle I π c hs.1
  have hv : chosenVertex I (reverseCycle π c) h' = chosenVertex I π h := by
    unfold chosenVertex
    simp only [hb]
  change (reverseCycle π c).cycleOf (chosenVertex I (reverseCycle π c) h') = c⁻¹
  rw [hv]
  exact (Equiv.Perm.cycle_is_cycleOf (by simpa [c] using hs.2.2.2)
    (inverse_mem_reverseCycle π c hs.1)).symm

def reverseBad (I : Finset V) (π : Equiv.Perm V) : Equiv.Perm V := by
  classical
  exact if h : (badVertices I π).Nonempty then reverseCycle π (chosenCycle I π h) else π

theorem badVertices_reverseBad (I : Finset V) (π : Equiv.Perm V) :
    badVertices I (reverseBad I π) = badVertices I π := by
  classical
  unfold reverseBad
  split_ifs with h
  · exact badVertices_reverseCycle I π _ (chosenCycle_spec I π h).1
  · rfl

theorem reverseBad_involution (I : Finset V) (π : Equiv.Perm V) :
    reverseBad I (reverseBad I π) = π := by
  classical
  by_cases h : (badVertices I π).Nonempty
  · have h' : (badVertices I (reverseCycle π (chosenCycle I π h))).Nonempty := by
      rwa [badVertices_reverseCycle I π _ (chosenCycle_spec I π h).1]
    simp only [reverseBad, dif_pos h, dif_pos h']
    rw [chosenCycle_reverse I π h h', reverseCycle_twice]
  · simp [reverseBad,h]

theorem reverseBad_outside (I : Finset V) (π : Equiv.Perm V) {v : V} (hv : v ∉ I) :
    reverseBad I π v = π v := by
  classical
  unfold reverseBad
  split_ifs with h
  · exact reverseCycle_outside π _ (fun hm => hv ((chosenCycle_spec I π h).2.1 hm))
  · rfl

end Chosen
end RandomOrderMatching.Algebra.Tutte.Representation
