import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
Finite submodularity and disjoint-demand deletion bounds.

`availability_submodular` proves that the maximum valuation of a basis among
available elements is submodular, assuming the established valuated-matroid
multiple exchange theorem as an EXPLICIT hypothesis. It verifies the two
exchanged bases' availability rather than postulating the objective inequality.

`sharp_deletion_bound` proves the complete finite disjoint-demand deduction
from submodularity, including empty and singleton families. The symbolic
weighted Tutte-minor representation is proved separately in Algebra.Tutte;
no such representation is declared as an axiom here.
-/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
namespace RandomOrderMatching.Algebra.Submodularity

variable {E V I : Type*} [DecidableEq E] [DecidableEq V] [DecidableEq I]

def Submodular (F : Finset V → ℝ) : Prop :=
  ∀ A B, F (A ∪ B) + F (A ∩ B) ≤ F A + F B

/-- Fixed always-available identity elements make every maximum finite.
The hypothesis `hmulti` is the standard multiple basis exchange theorem. -/
theorem availability_submodular
    (bases : Finset (Finset E)) (p : Finset E → ℝ) (D : Finset E)
    (g : Finset E → ℝ)
    (hattain : ∀ R, ∃ B ∈ bases, B ⊆ D ∪ R ∧ p B = g R)
    (hupper : ∀ R B, B ∈ bases → B ⊆ D ∪ R → p B ≤ g R)
    (hmulti : ∀ A ∈ bases, ∀ B ∈ bases, ∀ X ⊆ A \ B,
      ∃ Y ⊆ B \ A,
        (A \ X) ∪ Y ∈ bases ∧ (B \ Y) ∪ X ∈ bases ∧
        p A + p B ≤ p ((A \ X) ∪ Y) + p ((B \ Y) ∪ X)) :
    Submodular g := by
  intro U V
  obtain ⟨BU,hBU,hBUavail,hBUval⟩ := hattain (U ∪ V)
  obtain ⟨BI,hBI,hBIavail,hBIval⟩ := hattain (U ∩ V)
  let X := BU \ (D ∪ U)
  have hX : X ⊆ BU \ BI := by
    intro e he
    obtain ⟨heBU,heDU⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_sdiff.mpr ⟨heBU,?_⟩
    intro heBI
    have he := hBIavail heBI
    simp only [Finset.mem_union, Finset.mem_inter] at he
    exact heDU (Finset.mem_union.mpr (he.imp_right And.left))
  obtain ⟨Y,hY,hBA,hBB,hval⟩ := hmulti BU hBU BI hBI X hX
  have hBAavail : (BU \ X) ∪ Y ⊆ D ∪ U := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨heBU,heX⟩ := Finset.mem_sdiff.mp he
      by_contra h
      exact heX (Finset.mem_sdiff.mpr ⟨heBU,h⟩)
    · have heBI := (Finset.mem_sdiff.mp (hY he)).1
      have he := hBIavail heBI
      simp only [Finset.mem_union, Finset.mem_inter] at he ⊢
      exact he.imp_right And.left
  have hBBavail : (BI \ Y) ∪ X ⊆ D ∪ V := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · have heBI := (Finset.mem_sdiff.mp he).1
      have he := hBIavail heBI
      simp only [Finset.mem_union, Finset.mem_inter] at he ⊢
      exact he.imp_right And.right
    · obtain ⟨heBU,heDU⟩ := Finset.mem_sdiff.mp he
      have he := hBUavail heBU
      simp only [Finset.mem_union] at he heDU ⊢
      tauto
  have ha := hupper U _ hBA hBAavail
  have hb := hupper V _ hBB hBBavail
  rw [hBUval,hBIval] at hval
  linarith

/-- Complementation preserves submodularity on subsets of a finite universe. -/
theorem complement_submodular (F : Finset V → ℝ) (hF : Submodular F)
    (W : Finset V) : Submodular (fun S => F (W \ S)) := by
  intro A B
  have hh := hF (W \ A) (W \ B)
  have hu : (W \ A) ∪ (W \ B) = W \ (A ∩ B) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hi : (W \ A) ∩ (W \ B) = W \ (A ∪ B) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hu,hi] at hh
  linarith

theorem disjoint_two_defects (F : Finset V → ℝ) (hF : Submodular F)
    (A B : Finset V) (hd : Disjoint A B) :
    (F ∅ - F A) + (F ∅ - F B) ≤ F ∅ - F (A ∪ B) := by
  have hh := hF A B
  rw [Finset.disjoint_iff_inter_eq_empty.mp hd] at hh
  linarith

/-- No cardinality restriction on each demand. The empty family is included. -/
theorem disjoint_sum_defects (F : Finset V → ℝ) (hF : Submodular F)
    (S : Finset I) (X : I → Finset V)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (X i) (X j)) :
    (∑ i ∈ S, (F ∅ - F (X i))) ≤ F ∅ - F (S.biUnion X) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hdS : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → Disjoint (X j) (X k) := by
      intro j hj k hk hjk
      exact hd j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    have hdi : Disjoint (X i) (S.biUnion X) := by
      apply Finset.disjoint_left.mpr
      intro v hvX hvU
      obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp hvU
      have hne : i ≠ j := by intro h; subst j; exact hi hj
      exact Finset.disjoint_left.mp
        (hd i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hne)
        hvX hvj
    have hs := ih hdS
    have hh := disjoint_two_defects F hF (X i) (S.biUnion X) hdi
    rw [Finset.sum_insert hi, Finset.biUnion_insert]
    linarith

/-- The sharp deletion inequality follows from the submodular marked
path value and the immediate one-demand upper bound. -/
theorem sharp_deletion_bound
    (F : Finset V → ℝ) (hF : Submodular F) (q : ℝ)
    (hzero : F ∅ = 2*q) (S : Finset I) (X : I → Finset V)
    (deletedOpt : I → ℝ)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (X i) (X j))
    (hone : ∀ i ∈ S, F (X i) ≤ q + deletedOpt i)
    (a b : ℝ) (hpair : a+b ≤ F (S.biUnion X)) :
    (∑ i ∈ S, (q-deletedOpt i)) ≤ 2*q-a-b := by
  have hlocal : (∑ i ∈ S, (q-deletedOpt i)) ≤
      ∑ i ∈ S, (F ∅ - F (X i)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [hzero]
    linarith [hone i hi]
  have hsum := disjoint_sum_defects F hF S X hd
  rw [hzero] at hsum hlocal
  linarith

/-- Weighted B is a consequence, although integral occurrence splitting
is false. This release step also allows an arbitrary-size subset X. -/
theorem release_gain (F : Finset V → ℝ) (hF : Submodular F)
    (q qX : ℝ) (hzero : F ∅ = 2*q)
    (M X : Finset V) (hXM : X ⊆ M) (hone : F X ≤ q+qX) :
    q-qX ≤ F (M \ X)-F M := by
  have hd : Disjoint (M \ X) X := by
    apply Finset.disjoint_left.mpr
    intro v hv hx
    exact (Finset.mem_sdiff.mp hv).2 hx
  have hu : (M \ X) ∪ X = M := Finset.sdiff_union_of_subset hXM
  have hh := hF (M \ X) X
  rw [hu,Finset.disjoint_iff_inter_eq_empty.mp hd,hzero] at hh
  linarith

end RandomOrderMatching.Algebra.Submodularity
