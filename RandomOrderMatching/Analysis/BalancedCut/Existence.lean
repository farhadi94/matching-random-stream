import RandomOrderMatching.Analysis.BalancedCut.Concentration

/-! Actual simultaneous balanced-cut existence and a fixed canonical
choice at the exact degree-profile certificate parameters. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Analysis.BalancedCut
open RandomOrderMatching.Graph RandomOrderMatching.Analysis.BalancedCut.DegreeInterface

def beta0 (κ L : ℕ) : ℝ := (10^30:ℝ)*κ*L
def tolerance : ℝ := 1/10^10

theorem beta0_large (κ L : ℕ) (hk : 1≤κ) (hL : 1≤L) :
    (10^22:ℝ)≤beta0 κ L := by
  have hk' : (1:ℝ)≤κ := by exact_mod_cast hk
  have hL' : (1:ℝ)≤L := by exact_mod_cast hL
  have hprod : (1:ℝ)≤(κ:ℝ)*L := by nlinarith
  unfold beta0
  nlinarith

theorem final_failure_lt_one {n δ : ℝ} (κ L : ℕ)
    (hn : 2≤n) (hδ : 0<δ) (hδ1 : δ<1)
    (hk : 1≤κ) (hlog : Real.log (100*n/δ)≤L) :
    4*n*Real.exp (-2*tolerance^2*beta0 κ L)<1 := by
  obtain ⟨hL0,hbase⟩ := RandomOrderMatching.batch_failure_base hn hδ hδ1 hlog
  have hk' : (1:ℝ)≤κ := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_right hk' hL0
  have he : -2*tolerance^2*beta0 κ L≤-(L:ℝ) := by
    unfold tolerance beta0
    nlinarith
  have hexp := Real.exp_le_exp.mpr he
  have hn0 : 0<n := by linarith
  have hb : 4*n*Real.exp (-(L:ℝ))≤δ/25 := by
    calc
      _ ≤ 4*n*(δ/(100*n)) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by field_simp; ring
  have hh := mul_le_mul_of_nonneg_left hexp (show 0≤4*n by positivity)
  linarith

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

def Balanced (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X→V) (β : ℝ) (ω : Block M→Bool) : Prop :=
  ∀ x, (H.degree x : ℝ)/2-tolerance*β ≤
      ((cutGraph H (fun y=>side M hM ω (parent y))).degree x : ℝ) ∧
    ((cutGraph H (fun y=>side M hM ω (parent y))).degree x : ℝ) ≤
      (H.degree x : ℝ)/2+tolerance*β+1/2

theorem degree_le_of_edge_upper (H : SimpleGraph X) [DecidableRel H.Adj]
    {β : ℝ} (hβ : 0≤β)
    (hupper : ∀ x y,H.Adj x y→(H.degree x : ℝ)+H.degree y≤β) :
    ∀ x,(H.degree x : ℝ)≤β := by
  intro x
  by_cases hz : H.degree x=0
  · simpa [hz] using hβ
  · obtain ⟨y,hy⟩ := (SimpleGraph.degree_pos_iff_exists_adj H x).mp (Nat.pos_of_ne_zero hz)
    have hh := hupper x y hy
    have hy0 : (0:ℝ)≤H.degree y := Nat.cast_nonneg _
    linarith

/-- Every actual valid copied graph has a simultaneous balanced
original-consistent orientation. No balance event is assumed. -/
theorem exists_balanced_orientation (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X→V)
    (hnoloop : ∀ x y,H.Adj x y→parent x≠parent y)
    (hinj : ∀ x,Set.InjOn parent (H.neighborFinset x : Set X))
    (κ L : ℕ) (hk : 1≤κ) (hL : 1≤L) (n δ : ℝ)
    (hn : 2≤n) (hcard : (Fintype.card X : ℝ)≤n) (hδ : 0<δ) (hδ1 : δ<1)
    (hlog : Real.log (100*n/δ)≤L)
    (hupper : ∀ x y,H.Adj x y→(H.degree x : ℝ)+H.degree y≤beta0 κ L) :
    ∃ ω : Block M→Bool, Balanced M hM H parent (beta0 κ L) ω := by
  have hb : 0<beta0 κ L := lt_of_lt_of_le (by norm_num) (beta0_large κ L hk hL)
  have ht : 0<tolerance*beta0 κ L := mul_pos (by norm_num [tolerance]) hb
  have hd := degree_le_of_edge_upper H hb.le hupper
  have hh := actual_simultaneous_bad_bound M hM H parent hnoloop hinj hb ht hd
  have heq : -2*(tolerance*beta0 κ L)^2/beta0 κ L =
      -2*tolerance^2*beta0 κ L := by field_simp
  rw [heq] at hh
  have hcard' : 4*(Fintype.card X : ℝ)*Real.exp (-2*tolerance^2*beta0 κ L) ≤
      4*n*Real.exp (-2*tolerance^2*beta0 κ L) := by
    gcongr
  have hlt := (hh.trans hcard').trans_lt (final_failure_lt_one κ L hn hδ hδ1 hk hlog)
  by_contra hnone
  have hall : (⋃ x,vertexBad M hM H parent x (tolerance*beta0 κ L))=Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    have hnot : ¬Balanced M hM H parent (beta0 κ L) ω := fun h => hnone ⟨ω,h⟩
    obtain ⟨x,hx⟩ := not_forall.mp hnot
    exact Set.mem_iUnion.mpr ⟨x,hx⟩
  rw [hall,probReal_univ] at hlt
  exact (lt_irrefl (1:ℝ)) hlt

def canonicalOrientation (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X→V)
    (hnoloop : ∀ x y,H.Adj x y→parent x≠parent y)
    (hinj : ∀ x,Set.InjOn parent (H.neighborFinset x : Set X))
    (κ L : ℕ) (hk : 1≤κ) (hL : 1≤L) (n δ : ℝ)
    (hn : 2≤n) (hcard : (Fintype.card X : ℝ)≤n) (hδ : 0<δ) (hδ1 : δ<1)
    (hlog : Real.log (100*n/δ)≤L)
    (hupper : ∀ x y,H.Adj x y→(H.degree x : ℝ)+H.degree y≤beta0 κ L) : Block M→Bool :=
  (exists_balanced_orientation M hM H parent hnoloop hinj κ L hk hL n δ hn hcard
    hδ hδ1 hlog hupper).choose

theorem canonicalOrientation_balanced (M : Graph V) (hM : Matching M) (H : SimpleGraph X)
    [DecidableRel H.Adj] (parent : X→V)
    (hnoloop : ∀ x y,H.Adj x y→parent x≠parent y)
    (hinj : ∀ x,Set.InjOn parent (H.neighborFinset x : Set X))
    (κ L : ℕ) (hk : 1≤κ) (hL : 1≤L) (n δ : ℝ)
    (hn : 2≤n) (hcard : (Fintype.card X : ℝ)≤n) (hδ : 0<δ) (hδ1 : δ<1)
    (hlog : Real.log (100*n/δ)≤L)
    (hupper : ∀ x y,H.Adj x y→(H.degree x : ℝ)+H.degree y≤beta0 κ L) :
    Balanced M hM H parent (beta0 κ L)
      (canonicalOrientation M hM H parent hnoloop hinj κ L hk hL n δ hn hcard
        hδ hδ1 hlog hupper) :=
  (exists_balanced_orientation M hM H parent hnoloop hinj κ L hk hL n δ hn hcard
    hδ hδ1 hlog hupper).choose_spec

end RandomOrderMatching.Analysis.BalancedCut
