import RobustMatching.R7CopyDualClipped
import RobustMatching.R7CopyDualRefold

/-! Forward unfolding with exact cardinality. Together with arbitrary-copy
refolding this proves the value-preserving bipartite unfolding interface. -/
open scoped BigOperators
noncomputable section
namespace RobustMatching.R7CopyDual
open RobustMatching.Dual RobustMatching.R6FableSharpDualCopy
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def antidiagonal (W : ℕ) (e : L × R) (t : ℕ) : Finset ((L × Fin W) × (R × Fin W)) :=
  Finset.univ.filter (fun f => parent f=e ∧ f.1.2.val+f.2.2.val+1=t)

theorem antidiagonal_card (W : ℕ) (e : L × R) (t : ℕ) (ht : t ≤ W) :
    (antidiagonal W e t).card=t := by
  classical
  let f : Fin t → (L × Fin W) × (R × Fin W) := fun i =>
    ((e.1,⟨i.val,by omega⟩),(e.2,⟨t-1-i.val,by have hi := i.isLt; omega⟩))
  have hinj : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun z => z.1.2.val) h
  have himage : Finset.univ.image f=antidiagonal W e t := by
    ext g
    constructor
    · intro hg
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hg
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_⟩
      · rfl
      · have hi := i.isLt; dsimp [f]; omega
    · intro hg
      obtain ⟨_,hp,hi⟩ := Finset.mem_filter.mp hg
      have hil : g.1.2.val<t := by omega
      refine Finset.mem_image.mpr ⟨⟨g.1.2.val,hil⟩,Finset.mem_univ _,?_⟩
      have hL : g.1.1=e.1 := congrArg (fun z : L × R => z.1) hp
      have hR : g.2.1=e.2 := congrArg (fun z : L × R => z.2) hp
      apply Prod.ext
      · apply Prod.ext hL.symm
        apply Fin.ext
        rfl
      · apply Prod.ext hR.symm
        apply Fin.ext
        dsimp [f]
        omega
  rw [← himage,Finset.card_image_of_injective _ hinj]
  simp

def fullCopies (W : ℕ) (E : Finset (L × R)) (w : L × R → ℕ) :
    Finset ((L × Fin W) × (R × Fin W)) := by
  classical
  exact Finset.univ.filter (fun f => f ∈ CopyEdges W (E : Set (L × R)) w)

omit [DecidableEq L] [DecidableEq R] in
theorem fullCopies_parent (W : ℕ) (E : Finset (L × R)) (w : L × R → ℕ)
    (f : (L × Fin W) × (R × Fin W)) (hf : f ∈ fullCopies W E w) : parent f ∈ E := by
  classical
  exact (Finset.mem_filter.mp hf).2.1

omit [DecidableEq L] [DecidableEq R] in
theorem fullCopies_indices (W : ℕ) (E : Finset (L × R)) (w : L × R → ℕ)
    (f : (L × Fin W) × (R × Fin W)) (hf : f ∈ fullCopies W E w) :
    f.1.2.val+f.2.2.val+1=w (parent f) := by
  classical
  exact (Finset.mem_filter.mp hf).2.2

theorem fullCopies_fiber (W : ℕ) (E : Finset (L × R)) (w : L × R → ℕ)
    (e : L × R) (he : e ∈ E) : rootFiber (fullCopies W E w) e=antidiagonal W e (w e) := by
  ext f
  simp only [rootFiber,fullCopies,antidiagonal,Finset.mem_filter,Finset.mem_univ,true_and]
  change ((parent f ∈ E ∧ f.1.2.val+f.2.2.val+1=w (parent f)) ∧ parent f=e) ↔
    parent f=e ∧ f.1.2.val+f.2.2.val+1=w e
  constructor
  · rintro ⟨⟨_,hi⟩,hp⟩; exact ⟨hp,hp ▸ hi⟩
  · rintro ⟨hp,hi⟩; exact ⟨⟨hp ▸ he,hp ▸ hi⟩,hp⟩

theorem fullCopies_card (W : ℕ) (E : Finset (L × R)) (w : L × R → ℕ)
    (hw : ∀ e ∈ E, w e ≤ W) : (fullCopies W E w).card=∑ e ∈ E, w e := by
  rw [Finset.card_eq_sum_card_fiberwise (fullCopies_parent W E w)]
  apply Finset.sum_congr rfl
  intro e he
  change (rootFiber (fullCopies W E w) e).card=w e
  rw [fullCopies_fiber W E w e he]
  exact antidiagonal_card W e (w e) (hw e he)

theorem fullCopies_matching (W : ℕ) (M : Finset (L × R)) (w : L × R → ℕ)
    (hm : IsMatching M) : IsMatching (fullCopies W M w) :=
  copy_subset_matching W w M hm (fullCopies W M w)
    (fullCopies_parent W M w) (fullCopies_indices W M w)

/-- Every original matching unfolds to a genuine copy matching with exactly
its integer weight as cardinality, including zero-weight originals. -/
theorem matching_unfolds_exactly (W : ℕ) (M : Finset (L × R)) (w : L × R → ℕ)
    (hm : IsMatching M) (hw : ∀ e ∈ M, w e ≤ W) :
    IsMatching (fullCopies W M w) ∧ (fullCopies W M w).card=∑ e ∈ M, w e :=
  ⟨fullCopies_matching W M w hm,fullCopies_card W M w hw⟩

end RobustMatching.R7CopyDual
#print axioms RobustMatching.R7CopyDual.matching_unfolds_exactly
