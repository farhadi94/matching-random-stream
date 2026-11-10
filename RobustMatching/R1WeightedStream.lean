import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A combinatorial core of the bounded-weight streaming reduction

Edges are represented by a finite type with left and right endpoint maps.
Being a matching means injectivity of each endpoint map on the edge set.
The results below prove that unfolding a weighted matching preserves
disjointness and has cardinality equal to its total integral weight. They also
prove the refold/unfold subgraph inclusion. The converse optimum equality and
weighted bipartite integrality theorem are literature dependencies, not
assumed or claimed as formalized here.
-/

open scoped BigOperators

namespace RobustMatching.R1WeightedStream

variable {E L R : Type*}

abbrev Copies (w : E → ℕ) := Σ e, Fin (w e)

def unfold (w : E → ℕ) (s : Finset E) : Finset (Copies w) :=
  s.sigma (fun _e ↦ Finset.univ)

def leftCopy (w : E → ℕ) (left : E → L) (x : Copies w) : L × ℕ :=
  (left x.1, x.2.val)

def rightCopy (w : E → ℕ) (right : E → R) (x : Copies w) : R × ℕ :=
  (right x.1, w x.1 - (x.2.val + 1))

def IsMatching (left : E → L) (right : E → R) (s : Finset E) : Prop :=
  Set.InjOn left (s : Set E) ∧ Set.InjOn right (s : Set E)

/-- Unfolding a set has exactly the sum of its integral edge weights copies. -/
theorem unfold_card (w : E → ℕ) (s : Finset E) :
    (unfold w s).card = ∑ e ∈ s, w e := by
  simp [unfold, Finset.card_sigma]

theorem mem_unfold (w : E → ℕ) (s : Finset E) (x : Copies w) :
    x ∈ unfold w s ↔ x.1 ∈ s := by
  simp [unfold]

/-- The antidiagonal edge indices of one weighted edge are distinct. -/
theorem antidiagonal_injective (w : ℕ) :
    Function.Injective (fun i : Fin w ↦ w - (i.val + 1)) := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  dsimp at h
  omega

/-- Every original weighted matching lifts to an actual matching of copies. -/
theorem unfold_isMatching (w : E → ℕ) (left : E → L) (right : E → R)
    (s : Finset E) (hs : IsMatching left right s) :
    IsMatching (leftCopy w left) (rightCopy w right) (unfold w s) := by
  constructor
  · intro x hx y hy hxy
    have he : x.1 = y.1 := hs.1 ((mem_unfold w s x).mp hx)
      ((mem_unfold w s y).mp hy) (congrArg Prod.fst hxy)
    cases x with
    | mk e i =>
      cases y with
      | mk f j =>
        dsimp at he
        subst f
        have hij : i = j := Fin.ext (congrArg Prod.snd hxy)
        subst j
        rfl
  · intro x hx y hy hxy
    have he : x.1 = y.1 := hs.2 ((mem_unfold w s x).mp hx)
      ((mem_unfold w s y).mp hy) (congrArg Prod.fst hxy)
    cases x with
    | mk e i =>
      cases y with
      | mk f j =>
        dsimp at he
        subst f
        have hij : i = j := antidiagonal_injective (w e) (congrArg Prod.snd hxy)
        subst j
        rfl

/-- Refolding remembers the original edge of every retained copy. -/
def refold [DecidableEq E] (w : E → ℕ) (t : Finset (Copies w)) : Finset E :=
  t.image Sigma.fst

/-- This inclusion is the exact monotonicity bridge used by the published
bipartite refolding inequality. It does not say a refolded set is a matching. -/
theorem subset_unfold_refold [DecidableEq E] (w : E → ℕ) (t : Finset (Copies w)) :
    t ⊆ unfold w (refold w t) := by
  intro x hx
  apply (mem_unfold w (refold w t) x).mpr
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Resource bound for a bounded-weight unfolding. -/
theorem unfold_card_le (w : E → ℕ) (s : Finset E) (W : ℕ)
    (hw : ∀ e ∈ s, w e ≤ W) :
    (unfold w s).card ≤ s.card * W := by
  rw [unfold_card]
  calc
    _ ≤ ∑ _e ∈ s, W := Finset.sum_le_sum hw
    _ = _ := by simp

/-- Loss from omitted buckets, rounding, and greedy combination. -/
theorem bucket_loss_bound (t : ℝ) (ht : 0 ≤ t) :
    1 - 5 * t ≤ (1 - t)^2 / (1 + 3 * t) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 + 3 * t)).mpr
  nlinarith [sq_nonneg t]

end RobustMatching.R1WeightedStream

#print axioms RobustMatching.R1WeightedStream.unfold_card
#print axioms RobustMatching.R1WeightedStream.unfold_isMatching
#print axioms RobustMatching.R1WeightedStream.subset_unfold_refold
#print axioms RobustMatching.R1WeightedStream.unfold_card_le
#print axioms RobustMatching.R1WeightedStream.bucket_loss_bound
