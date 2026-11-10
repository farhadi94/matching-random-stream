import RobustMatching.R8BalancedCutOrientation

/-! Actual copied-neighbor decomposition by original orientation blocks. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RobustMatching.R8BalancedCut
open RobustMatching.R2Cut

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

def neighborFiber (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (g : Block M) : Finset X :=
  (H.neighborFinset x).filter fun y => block M hM (parent y)=g

def crossingFiber (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (b : Bool) (g : Block M)
    (c : Bool) : Finset X :=
  (neighborFiber M hM H parent x g).filter fun y =>
    Bool.xor c (parity M hM (parent y)) ≠ b

theorem neighborFiber_sum (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) :
    ∑ g, (neighborFiber M hM H parent x g).card = H.degree x := by
  simpa [neighborFiber] using Finset.sum_card_fiberwise_eq_card_filter
    (H.neighborFinset x) Finset.univ (fun y => block M hM (parent y))

theorem crossingFiber_card_le_one (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X)
    (hinj : Set.InjOn parent (H.neighborFinset x : Set X))
    (b : Bool) (g : Block M) (c : Bool) :
    (crossingFiber M hM H parent x b g c).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro y hy z hz
  obtain ⟨hyF,hyB⟩ := Finset.mem_filter.mp hy
  obtain ⟨hzF,hzB⟩ := Finset.mem_filter.mp hz
  obtain ⟨hyH,hyG⟩ := Finset.mem_filter.mp hyF
  obtain ⟨hzH,hzG⟩ := Finset.mem_filter.mp hzF
  apply hinj hyH hzH
  apply block_parity_injective M hM (hyG.trans hzG.symm)
  cases hp : parity M hM (parent y) <;>
    cases hq : parity M hM (parent z) <;> cases b <;> cases c <;> simp_all

theorem crossingFiber_partition (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (b : Bool) (g : Block M) :
    (crossingFiber M hM H parent x b g false).card +
      (crossingFiber M hM H parent x b g true).card =
        (neighborFiber M hM H parent x g).card := by
  have hpred (y : X) :
      (Bool.xor true (parity M hM (parent y)) ≠ b) ↔
      ¬(Bool.xor false (parity M hM (parent y)) ≠ b) := by
    cases parity M hM (parent y) <;> cases b <;> decide
  unfold crossingFiber
  simp_rw [hpred]
  exact Finset.card_filter_add_card_filter_not _

theorem own_neighbor_crosses (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V)
    (hnoloop : ∀ x y, H.Adj x y → parent x≠parent y)
    (x y : X) (hy : y∈neighborFiber M hM H parent x (block M hM (parent x)))
    (ω : Block M → Bool) :
    side M hM ω (parent x) ≠ side M hM ω (parent y) := by
  obtain ⟨hyH,hyG⟩ := Finset.mem_filter.mp hy
  exact same_block_opposite M hM hyG.symm
    (hnoloop x y (by simpa using hyH)) ω

theorem own_fiber_card_le_one (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V)
    (hnoloop : ∀ x y, H.Adj x y → parent x≠parent y)
    (x : X) (hinj : Set.InjOn parent (H.neighborFinset x : Set X)) :
    (neighborFiber M hM H parent x (block M hM (parent x))).card ≤ 1 := by
  let ω : Block M → Bool := fun _ => false
  have heq : crossingFiber M hM H parent x (side M hM ω (parent x))
      (block M hM (parent x)) false =
      neighborFiber M hM H parent x (block M hM (parent x)) := by
    apply Finset.filter_eq_self.mpr
    intro y hy
    have hh := own_neighbor_crosses M hM H parent hnoloop x y hy ω
    simpa [side,ω,ne_comm] using hh
  rw [← heq]
  exact crossingFiber_card_le_one M hM H parent x hinj _ _ _

/-- A two-neighbor pair block contributes one crossing neighbor for each
orientation; it never contributes a variable with range two. -/
theorem double_fiber_constant (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X)
    (hinj : Set.InjOn parent (H.neighborFinset x : Set X)) (b : Bool) (g : Block M)
    (hcard : (neighborFiber M hM H parent x g).card=2) (c : Bool) :
    (crossingFiber M hM H parent x b g c).card=1 := by
  have h0 := crossingFiber_card_le_one M hM H parent x hinj b g false
  have h1 := crossingFiber_card_le_one M hM H parent x hinj b g true
  have hs := crossingFiber_partition M hM H parent x b g
  cases c <;> omega

def blockValue (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (b : Bool) (g : Block M)
    (c : Bool) : ℝ :=
  if g=block M hM (parent x) then 0
  else (crossingFiber M hM H parent x b g c).card

def blockRange (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (g : Block M) : ℝ :=
  if g=block M hM (parent x) ∨ neighborFiber M hM H parent x g=∅ then 0 else 1

theorem blockValue_bounds (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X)
    (hinj : Set.InjOn parent (H.neighborFinset x : Set X))
    (b : Bool) (g : Block M) (c : Bool) :
    blockValue M hM H parent x b g c ∈ Set.Icc 0 (blockRange M hM H parent x g) := by
  unfold blockValue blockRange
  by_cases hg : g=block M hM (parent x)
  · simp [hg]
  · by_cases he : neighborFiber M hM H parent x g=∅
    · simp [hg,he,crossingFiber]
    · simp only [hg,he,false_or,if_false,Set.mem_Icc]
      exact ⟨Nat.cast_nonneg _,by exact_mod_cast crossingFiber_card_le_one M hM H parent x hinj b g c⟩

theorem blockRange_sq_sum_le_degree (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) :
    ∑ g, (blockRange M hM H parent x g)^2 ≤ (H.degree x : ℝ) := by
  have hh : ∑ g, (blockRange M hM H parent x g)^2 ≤
      ∑ g, ((neighborFiber M hM H parent x g).card : ℝ) := by
    apply Finset.sum_le_sum
    intro g _
    unfold blockRange
    split_ifs with h
    · simpa using (Nat.cast_nonneg (α:=ℝ) (neighborFiber M hM H parent x g).card)
    · have hc : 1 ≤ (neighborFiber M hM H parent x g).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (not_or.mp h).2)
      simpa using (show (1:ℝ) ≤ (neighborFiber M hM H parent x g).card by exact_mod_cast hc)
  simpa only [← Nat.cast_sum,neighborFiber_sum] using hh

end RobustMatching.R8BalancedCut
