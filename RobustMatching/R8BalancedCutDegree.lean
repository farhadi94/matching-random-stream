import RobustMatching.R8BalancedCutFibers

/-! Exact equality between actual cut degrees and independent block sums,
including the forced neighbor from the focal original's benchmark pair. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical MeasureTheory
open scoped BigOperators
namespace RobustMatching.R8BalancedCut
open RobustMatching.R2Cut RobustMatching.R2BalancedCut

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

def mateCount (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) : ℕ :=
  (neighborFiber M hM H parent x (block M hM (parent x))).card

def fixedDegree (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (b : Bool)
    (ω : Block M → Bool) : ℝ :=
  mateCount M hM H parent x + ∑ g, blockValue M hM H parent x b g (ω g)

theorem actual_degree_eq_fixed (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V)
    (hnoloop : ∀ x y,H.Adj x y→parent x≠parent y)
    (x : X) (ω : Block M → Bool) :
    ((cutGraph H (fun y => side M hM ω (parent y))).degree x : ℝ) =
      fixedDegree M hM H parent x (side M hM ω (parent x)) ω := by
  let b := side M hM ω (parent x)
  let J := cutGraph H (fun y => side M hM ω (parent y))
  have hf (g : Block M) :
      ((neighborFiber M hM J parent x g).card : ℝ) =
        (if g=block M hM (parent x) then (mateCount M hM H parent x : ℝ) else 0) +
          blockValue M hM H parent x b g (ω g) := by
    by_cases hg : g=block M hM (parent x)
    · subst g
      have heq : neighborFiber M hM J parent x (block M hM (parent x)) =
          neighborFiber M hM H parent x (block M hM (parent x)) := by
        ext y
        simp only [neighborFiber,Finset.mem_filter]
        rw [SimpleGraph.mem_neighborFinset,SimpleGraph.mem_neighborFinset]
        change ((H.Adj x y ∧ side M hM ω (parent x)≠side M hM ω (parent y)) ∧
          block M hM (parent y)=block M hM (parent x)) ↔ _
        constructor
        · rintro ⟨⟨ha,_⟩,hb⟩
          exact ⟨ha,hb⟩
        · rintro ⟨ha,hb⟩
          exact ⟨⟨ha,own_neighbor_crosses M hM H parent hnoloop x y
            (Finset.mem_filter.mpr ⟨by simpa using ha,hb⟩) ω⟩,hb⟩
      simp [heq,mateCount,blockValue]
    · have heq : neighborFiber M hM J parent x g =
          crossingFiber M hM H parent x b g (ω g) := by
        ext y
        simp only [neighborFiber,crossingFiber,Finset.mem_filter]
        rw [SimpleGraph.mem_neighborFinset,SimpleGraph.mem_neighborFinset]
        change ((H.Adj x y ∧ side M hM ω (parent x)≠side M hM ω (parent y)) ∧
          block M hM (parent y)=g) ↔ _
        constructor
        · rintro ⟨⟨ha,hs⟩,hb⟩
          refine ⟨⟨ha,hb⟩,?_⟩
          simpa [side,hb,b,ne_comm] using hs
        · rintro ⟨⟨ha,hb⟩,hs⟩
          refine ⟨⟨ha,?_⟩,hb⟩
          simpa [side,hb,b,ne_comm] using hs
      simp [heq,blockValue,hg]
  have hs := neighborFiber_sum M hM J parent x
  have hsr : (J.degree x : ℝ) = ∑ g, ((neighborFiber M hM J parent x g).card : ℝ) := by
    exact_mod_cast hs.symm
  rw [hsr]
  simp_rw [hf]
  simp [fixedDegree,Finset.sum_add_distrib,b]

theorem integral_blockValue (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (b : Bool) (g : Block M) :
    (∫ c, blockValue M hM H parent x b g c ∂coinMeasure) =
      if g=block M hM (parent x) then 0
      else ((neighborFiber M hM H parent x g).card : ℝ)/2 := by
  rw [integral_coin]
  by_cases hg : g=block M hM (parent x)
  · simp [blockValue,hg]
  · simp only [blockValue,hg,if_false]
    congr 1
    exact_mod_cast crossingFiber_partition M hM H parent x b g

theorem block_mean_sum (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (b : Bool) :
    (∑ g, ∫ c, blockValue M hM H parent x b g c ∂coinMeasure) =
      ((H.degree x : ℝ) - mateCount M hM H parent x)/2 := by
  have heq (g : Block M) :
      ((neighborFiber M hM H parent x g).card : ℝ) =
      (if g=block M hM (parent x) then (mateCount M hM H parent x : ℝ) else 0) +
      2*(∫ c,blockValue M hM H parent x b g c ∂coinMeasure) := by
    rw [integral_blockValue]
    by_cases hg : g=block M hM (parent x)
    · simp [hg,mateCount]
    · simp only [hg,if_false,zero_add]
      ring
  have hs := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun g _ => heq g)
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,←Nat.cast_sum,neighborFiber_sum] at hs
  linarith

theorem fixedDegree_centered (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (b : Bool) (ω : Block M → Bool) :
    fixedDegree M hM H parent x b ω -
      ((H.degree x : ℝ)/2+(mateCount M hM H parent x : ℝ)/2) =
      ∑ g, (blockValue M hM H parent x b g (ω g) -
        ∫ c,blockValue M hM H parent x b g c ∂coinMeasure) := by
  rw [Finset.sum_sub_distrib,block_mean_sum]
  unfold fixedDegree
  ring

theorem fixedDegree_complement_centered
    (M : Graph V) (hM : Matching M) (H : SimpleGraph X) [DecidableRel H.Adj]
    (parent : X → V) (x : X) (b : Bool) (ω : Block M → Bool) :
    (H.degree x : ℝ)/2+(mateCount M hM H parent x : ℝ)/2 -
        fixedDegree M hM H parent x b ω =
      ∑ g, ((blockRange M hM H parent x g-blockValue M hM H parent x b g (ω g)) -
        ∫ c, (blockRange M hM H parent x g-blockValue M hM H parent x b g c) ∂coinMeasure) := by
  have hint (g : Block M) :
      (∫ c, (blockRange M hM H parent x g-blockValue M hM H parent x b g c) ∂coinMeasure) =
        blockRange M hM H parent x g -
          ∫ c,blockValue M hM H parent x b g c ∂coinMeasure := by
    rw [integral_coin,integral_coin]
    ring
  simp_rw [hint]
  have hs := fixedDegree_centered M hM H parent x b ω
  have heq : (∑ g, ((blockRange M hM H parent x g-blockValue M hM H parent x b g (ω g)) -
      (blockRange M hM H parent x g-∫ c,blockValue M hM H parent x b g c ∂coinMeasure))) =
      -(∑ g,(blockValue M hM H parent x b g (ω g) -
        ∫ c,blockValue M hM H parent x b g c ∂coinMeasure)) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [heq,←hs]
  ring

end RobustMatching.R8BalancedCut
