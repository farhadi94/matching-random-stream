import RobustMatching.R7AlgebraInterpretationCancellation
import RobustMatching.R7GraphInterpretationDefs

/-!
Weighted upper-witness extraction after actual odd-cycle cancellation.
The only remaining combinatorial conversion is exposed separately: an
internal-odd-cycle-free partial permutation has bipartite undirected support.
-/
noncomputable section
open scoped BigOperators
open Equiv Finset

namespace RobustMatching.R7AlgebraInterpretation
open RobustMatching.R7Algebra RobustMatching.R7AlgebraTutte
open RobustMatching.R7GraphInterpretation
variable {V K : Type*} [Fintype V] [LinearOrder V]

theorem intDegree_prod [Field K] {ι : Type*} (S : Finset ι) (f : ι → RatFunc K)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    (∏ i ∈ S, f i).intDegree = ∑ i ∈ S, (f i).intDegree := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfS : ∀ j ∈ S, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      RatFunc.intDegree_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr hfS), ih hfS]

theorem weightedTutte_ne_zero_iff (G : SimpleGraph V) (w : Sym2 V → ℕ) (u v : V) :
    weightedTutte G w u v ≠ 0 ↔ G.Adj u v := by
  classical
  by_cases ha : G.Adj u v
  · by_cases huv : u < v <;>
      simp [weightedTutte,ha,huv,weightedVariable_ne_zero]
  · simp [weightedTutte,ha]

theorem weightedTutte_degree (G : SimpleGraph V) (w : Sym2 V → ℕ) {u v : V}
    (ha : G.Adj u v) :
    (weightedTutte G w u v).intDegree = (w s(u,v) : ℤ) := by
  classical
  by_cases huv : u < v
  · simp [weightedTutte,ha,huv,weightedVariable_degree]
  · simp [weightedTutte,ha,huv,RatFunc.intDegree_neg,weightedVariable_degree,Sym2.eq_swap]

theorem partialTerm_ne_zero_entries [Field K] (I : Finset V) (A : Matrix V V (RatFunc K))
    (π : Equiv.Perm V) (hn : partialTerm I A π ≠ 0) :
    ∀ i ∈ I, A i (π i) ≠ 0 := by
  intro i hi hz
  apply hn
  unfold partialTerm partialProduct
  have hp : (∏ j, if j ∈ I then A j (π j) else 1) = 0 :=
    Finset.prod_eq_zero (f := fun j => if j ∈ I then A j (π j) else 1)
      (Finset.mem_univ i) (by simp [hi,hz])
  rw [hp,mul_zero]

theorem partialTerm_weighted_degree (I : Finset V) (G : SimpleGraph V)
    (w : Sym2 V → ℕ) (π : Equiv.Perm V)
    (hn : partialTerm I (weightedTutte G w) π ≠ 0) :
    (partialTerm I (weightedTutte G w) π).intDegree =
      ∑ i ∈ I, (w s(i,π i) : ℤ) := by
  have he := partialTerm_ne_zero_entries I (weightedTutte G w) π hn
  have hp : partialProduct I (weightedTutte G w) π ≠ 0 := by
    intro hz
    exact hn (by simp [partialTerm,hz])
  have hs : ((Equiv.Perm.sign π : ℤ) : RatFunc (EdgeField V)) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hsd : (((Equiv.Perm.sign π : ℤ) : RatFunc (EdgeField V))).intDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  unfold partialTerm
  rw [RatFunc.intDegree_mul hs hp,hsd,zero_add]
  unfold partialProduct
  rw [Finset.prod_ite_mem_eq,intDegree_prod I (fun i => weightedTutte G w i (π i)) he]
  apply Finset.sum_congr rfl
  intro i hi
  exact weightedTutte_degree G w ((weightedTutte_ne_zero_iff G w i (π i)).mp (he i hi))

def partialArcs (I : Finset V) (π : Equiv.Perm V) : Finset (V × V) :=
  I.image fun i => (i,π i)

theorem partialArcs_matching (I : Finset V) (π : Equiv.Perm V) :
    RobustMatching.Dual.IsMatching (partialArcs I π) := by
  constructor
  · intro e he f hf h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hf
    exact congrArg (fun i => (i,π i)) h
  · intro e he f hf h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hf
    exact congrArg (fun i => (i,π i)) (π.injective h)

theorem partialArcs_source (I : Finset V) (π : Equiv.Perm V) :
    sourceSupport (partialArcs I π) = I := by
  simp [sourceSupport,partialArcs,Finset.image_image,Function.comp_def]

theorem partialArcs_target (I : Finset V) (π : Equiv.Perm V) :
    targetSupport (partialArcs I π) = I.image π := by
  simp [targetSupport,partialArcs,Finset.image_image,Function.comp_def]

theorem completion_image_mem (I : Finset V) (ρ π : Equiv.Perm V)
    (hπ : π ∈ completionPerms I ρ) {i : V} (hi : i ∈ I) : π i ∈ I.image ρ := by
  classical
  by_contra hn
  have hv : ρ.symm (π i) ∉ I := by
    intro hh
    exact hn (Finset.mem_image.mpr ⟨_,hh,by simp⟩)
  have he := (mem_completionPerms I ρ π).mp hπ _ hv
  have he' : ρ.symm (π i) = i := π.injective (by simpa using he)
  apply hv
  rw [he']
  exact hi

theorem no_bad_internal_cycles (I : Finset V) (π : Equiv.Perm V)
    (hn : ¬(badVertices I π).Nonempty) (c : Equiv.Perm V)
    (hc : c ∈ π.cycleFactorsFinset) (hI : c.support ⊆ I) : Even c.support.card := by
  by_contra hno
  have ho : Odd c.support.card := Nat.not_even_iff_odd.mp hno
  obtain ⟨v,hv,_⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
  exact hn ⟨v,(mem_badVertices I π v).mpr ⟨c,hc,hI,ho,Equiv.Perm.mem_support.mpr hv⟩⟩

/-- A surviving actual determinant term gives a partial permutation of at
least the determinant degree, with every internal directed cycle even. -/
theorem weighted_completed_upper_witness (I : Finset V) (G : SimpleGraph V)
    (w : Sym2 V → ℕ) (ρ : Equiv.Perm V)
    (hn : (completedMatrix I (weightedTutte G w) ρ).det ≠ 0) :
    ∃ π ∈ completionPerms I ρ,
      (∀ i ∈ I, G.Adj i (π i)) ∧
      (∀ c ∈ π.cycleFactorsFinset, c.support ⊆ I → Even c.support.card) ∧
      (completedMatrix I (weightedTutte G w) ρ).det.intDegree ≤
        ∑ i ∈ I, (w s(i,π i) : ℤ) := by
  have hd := det_completedMatrix_without_odd_cycles I (weightedTutte G w)
    (weightedTutte_skew G w) ρ
  have hs : (∑ π ∈ (completionPerms I ρ).filter (fun π => ¬(badVertices I π).Nonempty),
      partialTerm I (weightedTutte G w) π) ≠ 0 := by rwa [←hd]
  obtain ⟨π,hπ,hpn,hdeg⟩ := exists_intDegree_summand _ _ hs
  obtain ⟨hcomp,hbad⟩ := Finset.mem_filter.mp hπ
  refine ⟨π,hcomp,?_,?_,?_⟩
  · intro i hi
    exact (weightedTutte_ne_zero_iff G w i (π i)).mp
      (partialTerm_ne_zero_entries I (weightedTutte G w) π hpn i hi)
  · intro c hc hI
    exact no_bad_internal_cycles I π hbad c hc hI
  · rwa [←hd,partialTerm_weighted_degree I G w π hpn] at hdeg

end RobustMatching.R7AlgebraInterpretation
