import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import RandomOrderMatching.Graph.BipartiteMatrix

/-! Actual two-stage clipping of a finite bipartite support matrix. The
result is supported on the input incidences, has every row/column load at
most one, and loses at most the raw outside overload. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair

variable {C O : Type*} [Fintype C] [Fintype O]

def rowLoad (f : C → O → ℝ) (c : C) : ℝ := ∑ x, f c x
def colLoad (f : C → O → ℝ) (x : O) : ℝ := ∑ c, f c x
def rowClip (f : C → O → ℝ) (c : C) (x : O) : ℝ :=
  f c x / max 1 (rowLoad f c)
def colClip (f : C → O → ℝ) (c : C) (x : O) : ℝ :=
  f c x / max 1 (colLoad f x)
def repaired (f : C → O → ℝ) : C → O → ℝ := colClip (rowClip f)
def mass (f : C → O → ℝ) : ℝ := ∑ c, ∑ x, f c x

lemma normalize_nonneg {a d : ℝ} (ha : 0 ≤ a) : 0 ≤ a / max 1 d :=
  div_nonneg ha (le_trans (by norm_num) (le_max_left _ _))

lemma normalize_le {a d : ℝ} (ha : 0 ≤ a) : a / max 1 d ≤ a := by
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _))).2
  nlinarith [le_max_left (1:ℝ) d]

lemma normalized_total {a : ℝ} (_ha : 0 ≤ a) : a / max 1 a = min a 1 := by
  by_cases h : a ≤ 1
  · simp [max_eq_left h, min_eq_left h]
  · have h1 : 1 ≤ a := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right h1, min_eq_right h1, div_self (by linarith)]

omit [Fintype C] in
lemma rowClip_nonneg (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) :
    ∀ c x, 0 ≤ rowClip f c x := fun c x => normalize_nonneg (hf c x)

omit [Fintype C] in
lemma rowClip_le (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) :
    ∀ c x, rowClip f c x ≤ f c x := fun c x => normalize_le (hf c x)

omit [Fintype C] in
lemma rowClip_row (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) (c : C) :
    rowLoad (rowClip f) c = min (rowLoad f c) 1 := by
  simp only [rowLoad, rowClip, ← Finset.sum_div]
  exact normalized_total (Finset.sum_nonneg fun x _ => hf c x)

omit [Fintype O] in
lemma colClip_nonneg (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) :
    ∀ c x, 0 ≤ colClip f c x := fun c x => normalize_nonneg (hf c x)

omit [Fintype O] in
lemma colClip_le (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) :
    ∀ c x, colClip f c x ≤ f c x := fun c x => normalize_le (hf c x)

omit [Fintype O] in
lemma colClip_col (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) (x : O) :
    colLoad (colClip f) x = min (colLoad f x) 1 := by
  simp only [colLoad, colClip, ← Finset.sum_div]
  exact normalized_total (Finset.sum_nonneg fun c _ => hf c x)

theorem repaired_nonneg (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) :
    ∀ c x, 0 ≤ repaired f c x := colClip_nonneg _ (rowClip_nonneg f hf)

theorem repaired_le (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) :
    ∀ c x, repaired f c x ≤ f c x := by
  intro c x
  exact le_trans (colClip_le _ (rowClip_nonneg f hf) c x) (rowClip_le f hf c x)

theorem repaired_support (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x)
    (adj : C → O → Prop) (hs : ∀ c x, ¬adj c x → f c x = 0) :
    ∀ c x, ¬adj c x → repaired f c x = 0 := by
  intro c x h
  apply le_antisymm
  · simpa [hs c x h] using repaired_le f hf c x
  · exact repaired_nonneg f hf c x

theorem repaired_row_le_one (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) (c : C) :
    rowLoad (repaired f) c ≤ 1 := by
  calc
    rowLoad (repaired f) c ≤ rowLoad (rowClip f) c :=
      Finset.sum_le_sum fun x _ => colClip_le _ (rowClip_nonneg f hf) c x
    _ = min (rowLoad f c) 1 := rowClip_row f hf c
    _ ≤ 1 := min_le_right _ _

theorem repaired_col_le_one (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) (x : O) :
    colLoad (repaired f) x ≤ 1 := by
  rw [repaired, colClip_col _ (rowClip_nonneg f hf)]
  exact min_le_right _ _

lemma sub_min_eq_overload (a : ℝ) : a-min a 1 = max (a-1) 0 := by
  by_cases h : a ≤ 1
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right (by linarith : 1 ≤ a), max_eq_left (by linarith)]

lemma mass_cols (f : C → O → ℝ) : mass f = ∑ x, colLoad f x := by
  unfold mass colLoad
  exact Finset.sum_comm

lemma colClip_loss (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) :
    mass f-mass (colClip f) = ∑ x, max (colLoad f x-1) 0 := by
  rw [mass_cols f, mass_cols (colClip f), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [colClip_col f hf, sub_min_eq_overload]

/-- The lower bound concerns the actual scaled matrix, not a supplied
fractional certificate. Each raw outside overload is charged only once. -/
theorem repaired_mass_lower (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x) :
    (∑ c, min (rowLoad f c) 1) - (∑ x, max (colLoad f x-1) 0) ≤
      mass (repaired f) := by
  have hrows : mass (rowClip f) = ∑ c, min (rowLoad f c) 1 := by
    apply Finset.sum_congr rfl
    intro c _
    exact rowClip_row f hf c
  have hc : ∀ x, colLoad (rowClip f) x ≤ colLoad f x := by
    intro x
    exact Finset.sum_le_sum fun c _ => rowClip_le f hf c x
  have hsum : (∑ x, max (colLoad (rowClip f) x-1) 0) ≤
      ∑ x, max (colLoad f x-1) 0 := by
    apply Finset.sum_le_sum
    intro x _
    exact max_le_max (sub_le_sub_right (hc x) 1) le_rfl
  have hloss := colClip_loss (rowClip f) (rowClip_nonneg f hf)
  rw [hrows] at hloss
  change (∑ c, min (rowLoad f c) 1) - (∑ x, max (colLoad f x-1) 0) ≤
    mass (colClip (rowClip f))
  linarith

/-- An actual matching in the input incidence graph attains the repair
mass lower bound; no matching or cover existence is assumed. -/
theorem repaired_matching [DecidableEq C] [DecidableEq O]
    (adj : C → O → Prop) [DecidableRel adj]
    (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x)
    (hs : ∀ c x, ¬adj c x → f c x = 0) :
    ∃ M : RandomOrderMatching.Graph.Graph (C ⊕ O),
      M ⊆ RandomOrderMatching.Graph.BipartiteMatrix.graphEdges adj ∧ RandomOrderMatching.Graph.Matching M ∧
      (∑ c, min (rowLoad f c) 1) - (∑ x, max (colLoad f x-1) 0) ≤ (M.card : ℝ) := by
  obtain ⟨M, hM, hmatch, hmass⟩ := RandomOrderMatching.Graph.BipartiteMatrix.matrix_rounding adj (repaired f)
    (repaired_nonneg f hf) (repaired_support f hf adj hs)
    (repaired_row_le_one f hf) (repaired_col_le_one f hf)
  exact ⟨M, hM, hmatch, le_trans (repaired_mass_lower f hf) hmass⟩

end RandomOrderMatching.Analysis.Repair
#print axioms RandomOrderMatching.Analysis.Repair.repaired_mass_lower
#print axioms RandomOrderMatching.Analysis.Repair.repaired_support
#print axioms RandomOrderMatching.Analysis.Repair.repaired_row_le_one
#print axioms RandomOrderMatching.Analysis.Repair.repaired_col_le_one
#print axioms RandomOrderMatching.Analysis.Repair.repaired_matching
