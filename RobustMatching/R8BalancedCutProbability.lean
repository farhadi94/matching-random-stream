import RobustMatching.R8BalancedCutDegree

/-! Simultaneous balance on the actual original-orientation experiment.
Both possible focal sides are bounded without a conditioning argument. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RobustMatching.R8BalancedCut
open RobustMatching.R2Cut RobustMatching.R2BalancedCut

theorem coin_sum_upper_tail {ι : Type*} [Fintype ι]
    (X : ι → Bool → ℝ) (a : ι → ℝ)
    (hb : ∀ i c,X i c∈Set.Icc 0 (a i)) {β t : ℝ}
    (hβ : 0<β) (ht : 0<t) (ha : ∑ i,(a i)^2≤β) :
    (Measure.pi (fun _ : ι => coinMeasure)).real
      {ω | t≤∑ i,(X i (ω i)-∫ c,X i c ∂coinMeasure)} ≤ Real.exp (-2*t^2/β) := by
  let D := ∑ i,(a i)^2
  have hD0 : 0≤D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hz : D=0
  · have ha0 (i : ι) : a i=0 := by
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))).mp hz
      exact sq_eq_zero_iff.mp (hh i (Finset.mem_univ _))
    have hx0 (i : ι) (c : Bool) : X i c=0 := by
      have hh := hb i c
      rw [ha0] at hh
      exact le_antisymm hh.2 hh.1
    have heq : {ω : ι→Bool | t≤∑ i,(X i (ω i)-∫ c,X i c ∂coinMeasure)} = ∅ := by
      ext ω
      simp [hx0,not_le.mpr ht]
    rw [heq]
    simp only [measureReal_empty]
    exact (Real.exp_pos _).le
  · have hD : 0<D := lt_of_le_of_ne hD0 (Ne.symm hz)
    have hh := RobustMatching.product_bounded_upper_tail (fun _ : ι => coinMeasure) X a
      (fun i => measurable_of_finite _) hb ht.le
    apply hh.trans (Real.exp_le_exp.mpr ?_)
    change -2*t^2/D ≤ -2*t^2/β
    apply (div_le_div_iff₀ hD hβ).mpr
    dsimp [D] at *
    nlinarith [sq_nonneg t]

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

theorem fixed_degree_upper_tail (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X)
    (hinj : Set.InjOn parent (H.neighborFinset x : Set X)) (b : Bool)
    {β t : ℝ} (hβ : 0<β) (ht : 0<t) (hd : (H.degree x : ℝ)≤β) :
    (experiment M).real {ω | t ≤ fixedDegree M hM H parent x b ω -
      ((H.degree x : ℝ)/2+(mateCount M hM H parent x : ℝ)/2)} ≤
        Real.exp (-2*t^2/β) := by
  simp_rw [fixedDegree_centered]
  exact coin_sum_upper_tail (blockValue M hM H parent x b) (blockRange M hM H parent x)
    (blockValue_bounds M hM H parent x hinj b) hβ ht
    ((blockRange_sq_sum_le_degree M hM H parent x).trans hd)

theorem fixed_degree_lower_tail (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X)
    (hinj : Set.InjOn parent (H.neighborFinset x : Set X)) (b : Bool)
    {β t : ℝ} (hβ : 0<β) (ht : 0<t) (hd : (H.degree x : ℝ)≤β) :
    (experiment M).real {ω | t ≤
      (H.degree x : ℝ)/2+(mateCount M hM H parent x : ℝ)/2 -
      fixedDegree M hM H parent x b ω} ≤ Real.exp (-2*t^2/β) := by
  simp_rw [fixedDegree_complement_centered]
  have hb : ∀ g c,
      blockRange M hM H parent x g - blockValue M hM H parent x b g c ∈
        Set.Icc 0 (blockRange M hM H parent x g) := by
    intro g c
    have hh := blockValue_bounds M hM H parent x hinj b g c
    constructor <;> linarith [hh.1,hh.2]
  exact coin_sum_upper_tail
    (fun g c => blockRange M hM H parent x g-blockValue M hM H parent x b g c)
    (blockRange M hM H parent x) hb hβ ht
    ((blockRange_sq_sum_le_degree M hM H parent x).trans hd)

def vertexBad (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V) (x : X) (t : ℝ) :
    Set (Block M → Bool) :=
  {ω | ¬((H.degree x : ℝ)/2-t ≤
      ((cutGraph H (fun y => side M hM ω (parent y))).degree x : ℝ) ∧
    ((cutGraph H (fun y => side M hM ω (parent y))).degree x : ℝ) ≤
      (H.degree x : ℝ)/2+t+1/2)}

theorem actual_vertex_bad_bound (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V)
    (hnoloop : ∀ x y,H.Adj x y→parent x≠parent y)
    (x : X) (hinj : Set.InjOn parent (H.neighborFinset x : Set X))
    {β t : ℝ} (hβ : 0<β) (ht : 0<t) (hd : (H.degree x : ℝ)≤β) :
    (experiment M).real (vertexBad M hM H parent x t) ≤ 4*Real.exp (-2*t^2/β) := by
  let B : Bool → Set (Block M → Bool) := fun b =>
    {ω | t ≤ fixedDegree M hM H parent x b ω -
      ((H.degree x : ℝ)/2+(mateCount M hM H parent x : ℝ)/2)} ∪
    {ω | t ≤ (H.degree x : ℝ)/2+(mateCount M hM H parent x : ℝ)/2 -
      fixedDegree M hM H parent x b ω}
  have hB (b : Bool) : (experiment M).real (B b) ≤ 2*Real.exp (-2*t^2/β) := by
    have h1 := fixed_degree_upper_tail M hM H parent x hinj b hβ ht hd
    have h2 := fixed_degree_lower_tail M hM H parent x hinj b hβ ht hd
    exact (measureReal_union_le _ _).trans (by linarith)
  have hs : vertexBad M hM H parent x t ⊆ ⋃ b,B b := by
    intro ω hω
    apply Set.mem_iUnion.mpr
    refine ⟨side M hM ω (parent x),?_⟩
    have heq := actual_degree_eq_fixed M hM H parent hnoloop x ω
    have hm0 : (0:ℝ)≤mateCount M hM H parent x := Nat.cast_nonneg _
    have hm1 : (mateCount M hM H parent x : ℝ)≤1 := by
      exact_mod_cast own_fiber_card_le_one M hM H parent hnoloop x hinj
    change ¬(_∧_) at hω
    rw [heq] at hω
    rcases not_and_or.mp hω with hl | hu
    · right
      change t≤_
      have hh := lt_of_not_ge hl
      linarith
    · left
      change t≤_
      have hh := lt_of_not_ge hu
      linarith
  calc
    _ ≤ (experiment M).real (⋃ b,B b) := measureReal_mono hs
    _ ≤ ∑ b,(experiment M).real (B b) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _b : Bool,2*Real.exp (-2*t^2/β) := Finset.sum_le_sum (fun b _ => hB b)
    _ = 4*Real.exp (-2*t^2/β) := by simp; ring

theorem actual_simultaneous_bad_bound (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X → V)
    (hnoloop : ∀ x y,H.Adj x y→parent x≠parent y)
    (hinj : ∀ x,Set.InjOn parent (H.neighborFinset x : Set X))
    {β t : ℝ} (hβ : 0<β) (ht : 0<t) (hd : ∀ x,(H.degree x : ℝ)≤β) :
    (experiment M).real (⋃ x,vertexBad M hM H parent x t) ≤
      4*(Fintype.card X : ℝ)*Real.exp (-2*t^2/β) := by
  calc
    _ ≤ ∑ x,(experiment M).real (vertexBad M hM H parent x t) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _x : X,4*Real.exp (-2*t^2/β) := Finset.sum_le_sum
      (fun x _ => actual_vertex_bad_bound M hM H parent hnoloop x (hinj x) hβ ht (hd x))
    _ = _ := by simp; ring

end RobustMatching.R8BalancedCut
