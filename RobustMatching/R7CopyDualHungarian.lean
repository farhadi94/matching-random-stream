import RobustMatching.R1DualLattice
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Int.LeastGreatest

/-! Integral weighted bipartite duality from finite Hall.
The core theorem constructs tight integer labels and a permutation. It does
not assume LP duality or existence of optimal price vectors. -/

open scoped BigOperators
noncomputable section
namespace RobustMatching.R7CopyDual

variable {I : Type*} [Fintype I] [DecidableEq I]

def labelCost (p q : I → ℤ) : ℤ := (∑ i, p i) + ∑ i, q i

def LabelFeasible (w : I → I → ℕ) (p q : I → ℤ) : Prop :=
  ∀ i j, (w i j : ℤ) ≤ p i + q j

omit [DecidableEq I] in
theorem labelCost_nonneg {w : I → I → ℕ} {p q : I → ℤ}
    (h : LabelFeasible w p q) : 0 ≤ labelCost p q := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i i)
  have hn : 0 ≤ ∑ i, (w i i : ℤ) := Finset.sum_nonneg (by intro i hi; omega)
  simpa only [Finset.sum_add_distrib, labelCost] using hn.trans hs

omit [DecidableEq I] in
theorem exists_min_labels (w : I → I → ℕ) :
    ∃ p q : I → ℤ, LabelFeasible w p q ∧
      ∀ p' q', LabelFeasible w p' q' → labelCost p q ≤ labelCost p' q' := by
  classical
  let P : ℤ → Prop := fun c => ∃ p q : I → ℤ, LabelFeasible w p q ∧ labelCost p q = c
  have hinit : LabelFeasible w (fun i => ∑ j, (w i j : ℤ)) (fun _ => 0) := by
    intro i j
    simpa using (Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
      (show (0 : ℤ) ≤ w i k by omega)) (Finset.mem_univ j))
  obtain ⟨c, ⟨p,q,hpq,hcost⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := P) ⟨0, by rintro z ⟨p,q,h,rfl⟩; exact labelCost_nonneg h⟩
    ⟨_, _, _, hinit, rfl⟩
  refine ⟨p,q,hpq,?_⟩
  intro p' q' h'
  rw [hcost]
  exact hmin _ ⟨p',q',h',rfl⟩

/-- Every minimum-cost integral labeling has a tight permutation. A failed
Hall set would admit an integral unit shift of strictly smaller cost. -/
theorem min_labels_tight_permutation (w : I → I → ℕ) (p q : I → ℤ)
    (hpq : LabelFeasible w p q)
    (hmin : ∀ p' q', LabelFeasible w p' q' → labelCost p q ≤ labelCost p' q') :
    ∃ f : I → I, Function.Bijective f ∧ ∀ i, (w i (f i) : ℤ) = p i + q (f i) := by
  classical
  let t : I → Finset I := fun i => Finset.univ.filter (fun j => (w i j : ℤ) = p i + q j)
  have hhall : ∀ s : Finset I, s.card ≤ (s.biUnion t).card := by
    intro s
    by_contra hn
    have hcard : (s.biUnion t).card < s.card := Nat.lt_of_not_ge hn
    let n := s.biUnion t
    let p' : I → ℤ := fun i => p i - if i ∈ s then 1 else 0
    let q' : I → ℤ := fun j => q j + if j ∈ n then 1 else 0
    have hf : LabelFeasible w p' q' := by
      intro i j
      have h := hpq i j
      by_cases hi : i ∈ s <;> by_cases hj : j ∈ n
      · simp only [p',q',if_pos hi,if_pos hj]; omega
      · have hneq : (w i j : ℤ) ≠ p i + q j := by
          intro heq
          exact hj (Finset.mem_biUnion.mpr ⟨i,hi,by simp [t,heq]⟩)
        simp only [p',q',if_pos hi,if_neg hj]
        omega
      · simp only [p',q',if_neg hi,if_pos hj]; omega
      · simp only [p',q',if_neg hi,if_neg hj]; omega
    have hcost : labelCost p' q' = labelCost p q - (s.card : ℤ) + n.card := by
      simp [labelCost,p',q',Finset.sum_sub_distrib,Finset.sum_add_distrib]
      ring
    have hm := hmin p' q' hf
    rw [hcost] at hm
    have hc : (n.card : ℤ) < s.card := by exact_mod_cast hcard
    omega
  obtain ⟨f,hf,hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  refine ⟨f, ⟨hf, Finite.surjective_of_injective hf⟩, ?_⟩
  intro i
  exact (Finset.mem_filter.mp (hmem i)).2

theorem exists_integral_assignment_dual (w : I → I → ℕ) :
    ∃ (p q : I → ℤ) (f : I → I), LabelFeasible w p q ∧
      Function.Bijective f ∧ (∀ i, (w i (f i) : ℤ) = p i + q (f i)) ∧
      labelCost p q = ∑ i, (w i (f i) : ℤ) := by
  obtain ⟨p,q,hpq,hmin⟩ := exists_min_labels w
  obtain ⟨f,hf,ht⟩ := min_labels_tight_permutation w p q hpq hmin
  refine ⟨p,q,f,hpq,hf,ht,?_⟩
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  have hs : (∑ i, q (f i)) = ∑ i, q i := (Equiv.ofBijective f hf).sum_comp q
  rw [hs]
  rfl

/-- Nonnegative integral labels are obtained by a constant gauge shift.
Completeness and nonnegative weights make every shifted right label
nonnegative. Empty square instances are handled separately. -/
theorem exists_nat_assignment_dual (w : I → I → ℕ) :
    ∃ (p q : I → ℕ) (f : I → I),
      (∀ i j, w i j ≤ p i + q j) ∧ Function.Bijective f ∧
      (∀ i, w i (f i) = p i + q (f i)) ∧
      (∑ i, p i) + (∑ i, q i) = ∑ i, w i (f i) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hi =>
      let := hi
      refine ⟨fun _ => 0, fun _ => 0, id, ?_, Function.bijective_id, ?_, ?_⟩
      · intro i; exact isEmptyElim i
      · intro i; exact isEmptyElim i
      · simp
  | inr hi =>
      let := hi
      obtain ⟨p,q,f,hpq,hf,ht,_⟩ := exists_integral_assignment_dual w
      obtain ⟨i0,_,hsmall⟩ := Finset.exists_min_image Finset.univ p Finset.univ_nonempty
      have hpn (i : I) : 0 ≤ p i - p i0 := sub_nonneg.mpr (hsmall i (Finset.mem_univ i))
      have hqn (j : I) : 0 ≤ q j + p i0 := by have h := hpq i0 j; omega
      let pn : I → ℕ := fun i => (p i - p i0).toNat
      let qn : I → ℕ := fun j => (q j + p i0).toNat
      have hpc (i : I) : (pn i : ℤ) = p i - p i0 := Int.toNat_of_nonneg (hpn i)
      have hqc (j : I) : (qn j : ℤ) = q j + p i0 := Int.toNat_of_nonneg (hqn j)
      have hnat (i j : I) : w i j ≤ pn i + qn j := by
        have h := hpq i j
        have hp := hpc i
        have hq := hqc j
        omega
      have htnat (i : I) : w i (f i) = pn i + qn (f i) := by
        have h := ht i
        have hp := hpc i
        have hq := hqc (f i)
        omega
      refine ⟨pn,qn,f,hnat,hf,htnat,?_⟩
      simp_rw [htnat]
      rw [Finset.sum_add_distrib]
      have hs : (∑ i, qn (f i)) = ∑ i, qn i := (Equiv.ofBijective f hf).sum_comp qn
      rw [hs]

section Bipartite
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
open RobustMatching.Dual

theorem nat_matching_weak_duality (E M : Finset (L × R)) (w : L × R → ℕ)
    (p : L → ℕ) (q : R → ℕ) (hm : IsMatching M) (hsub : M ⊆ E)
    (hfeas : ∀ e ∈ E, w e ≤ p e.1 + q e.2) :
    (∑ e ∈ M, w e) ≤ (∑ l, p l) + ∑ r, q r := by
  have he := Finset.sum_le_sum (fun e he => hfeas e (hsub he))
  rw [Finset.sum_add_distrib] at he
  have hl : (∑ e ∈ M, p e.1) ≤ ∑ l, p l := by
    rw [← Finset.sum_image (f := p) hm.1]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hr : (∑ e ∈ M, q e.2) ≤ ∑ r, q r := by
    rw [← Finset.sum_image (f := q) hm.2]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

/-- An actual maximum-weight bipartite matching and a nonnegative integral
dual of exactly the same weight, obtained by zero-padding the square
assignment theorem. No matching optimum or dual-existence premise occurs. -/
theorem exists_nat_bipartite_dual (E : Finset (L × R)) (w : L × R → ℕ) :
    ∃ (M : Finset (L × R)) (p : L → ℕ) (q : R → ℕ),
      IsMatching M ∧ M ⊆ E ∧ (∀ e ∈ E, w e ≤ p e.1 + q e.2) ∧
      (∑ e ∈ M, w e) = (∑ l, p l) + ∑ r, q r := by
  classical
  let a : L ⊕ R → L ⊕ R → ℕ := fun i j =>
    match i,j with
    | .inl l, .inr r => if (l,r) ∈ E then w (l,r) else 0
    | _,_ => 0
  obtain ⟨p,q,f,hfeas,hf,ht,hcost⟩ := exists_nat_assignment_dual a
  let M := E.filter (fun e => f (.inl e.1) = .inr e.2)
  have hsub : M ⊆ E := Finset.filter_subset _ _
  have hmatch (e : L × R) (he : e ∈ M) : f (.inl e.1) = .inr e.2 :=
    (Finset.mem_filter.mp he).2
  have hm : IsMatching M := by
    constructor
    · intro e he z hz hleft
      apply Prod.ext hleft
      have h := (hmatch e he).symm.trans ((congrArg (fun l => f (.inl l)) hleft).trans (hmatch z hz))
      exact Sum.inr.inj h
    · intro e he z hz hright
      apply Prod.ext _ hright
      apply Sum.inl.inj
      apply hf.1
      rw [hmatch e he,hmatch z hz,hright]
  have hfa (e : L × R) (he : e ∈ M) : a (.inl e.1) (f (.inl e.1)) = w e := by
    rw [hmatch e he]
    simp [a,hsub he]
  let g : L ⊕ R → ℕ := fun i => a i (f i)
  have hinj : Set.InjOn (fun e : L × R => (Sum.inl e.1 : L ⊕ R)) (M : Set (L × R)) := by
    intro e he z hz heq
    exact hm.1 he hz (Sum.inl.inj heq)
  have hzero : ∀ i ∈ (Finset.univ : Finset (L ⊕ R)),
      i ∉ M.image (fun e => (Sum.inl e.1 : L ⊕ R)) → g i = 0 := by
    intro i _ hi
    cases i with
    | inr r => simp [g,a]
    | inl l =>
      cases hfl : f (.inl l) with
      | inl l' => simp [g,a,hfl]
      | inr r =>
        have hn : (l,r) ∉ E := by
          intro he
          apply hi
          exact Finset.mem_image.mpr ⟨(l,r),by simp [M,he,hfl],rfl⟩
        simp [g,a,hfl,hn]
  have hweight : (∑ e ∈ M, w e) = ∑ i, a i (f i) := by
    calc
      (∑ e ∈ M, w e) = ∑ e ∈ M, g (.inl e.1) := Finset.sum_congr rfl (by
        intro e he; exact (hfa e he).symm)
      _ = ∑ i ∈ M.image (fun e => (Sum.inl e.1 : L ⊕ R)), g i :=
        (Finset.sum_image hinj).symm
      _ = ∑ i, g i := Finset.sum_subset (Finset.subset_univ _) hzero
  let pl : L → ℕ := fun l => p (.inl l)
  let qr : R → ℕ := fun r => q (.inr r)
  have hfe (e : L × R) (he : e ∈ E) : w e ≤ pl e.1 + qr e.2 := by
    have h := hfeas (.inl e.1) (.inr e.2)
    simpa [a,he,pl,qr] using h
  refine ⟨M,pl,qr,hm,hsub,hfe,?_⟩
  apply Nat.le_antisymm (nat_matching_weak_duality E M w pl qr hm hsub hfe)
  rw [hweight,← hcost]
  simp only [Fintype.sum_sum_type]
  dsimp [pl,qr]
  omega

end Bipartite

end RobustMatching.R7CopyDual

#print axioms RobustMatching.R7CopyDual.exists_integral_assignment_dual
#print axioms RobustMatching.R7CopyDual.exists_nat_bipartite_dual
