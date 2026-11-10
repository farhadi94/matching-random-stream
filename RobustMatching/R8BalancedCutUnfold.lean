import RobustMatching.R8BalancedCutExistence

/-! Canonical general-graph unfolding supplies the structural neighbor
properties; balanced-cut existence then needs only the frozen acquisition
degree inequalities. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RobustMatching.R8BalancedCut
open RobustMatching.R2Cut RobustMatching.R2BalancedCut

variable {V : Type*} [Fintype V] [DecidableEq V]

def unfolding (G : SimpleGraph V) (w : Sym2 V→ℕ) (W : ℕ) :
    SimpleGraph (V×Fin W) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2.val+y.2.val+1=w s(x.1,y.1)
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    simpa [Sym2.eq_swap,Nat.add_comm] using h.2⟩
  loopless := ⟨by intro x h; exact G.irrefl h.1⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (w : Sym2 V→ℕ) (W : ℕ) :
    DecidableRel (unfolding G w W).Adj := by
  intro x y
  change Decidable (G.Adj x.1 y.1 ∧ x.2.val+y.2.val+1=w s(x.1,y.1))
  infer_instance

theorem unfolding_original_ne (G : SimpleGraph V) (w : Sym2 V→ℕ) (W : ℕ)
    (H : SimpleGraph (V×Fin W)) (hH : H≤unfolding G w W)
    (x y : V×Fin W) (hxy : H.Adj x y) : x.1≠y.1 :=
  (hH hxy).1.ne

theorem unfolding_neighbor_parent_injective (G : SimpleGraph V) (w : Sym2 V→ℕ) (W : ℕ)
    (H : SimpleGraph (V×Fin W)) [DecidableRel H.Adj] (hH : H≤unfolding G w W)
    (x : V×Fin W) : Set.InjOn Prod.fst (H.neighborFinset x : Set (V×Fin W)) := by
  intro y hy z hz hyz
  have ha := (hH (show H.Adj x y by simpa using hy)).2
  have hb := (hH (show H.Adj x z by simpa using hz)).2
  change y.1=z.1 at hyz
  rw [hyz] at ha
  apply Prod.ext hyz
  apply Fin.ext
  omega

/-- A fixed original cut, selected solely from the frozen graph, benchmark
and parameter data. No suffix order or future repair event is an input. -/
def canonicalCopySide (G : SimpleGraph V) (w : Sym2 V→ℕ) (W : ℕ)
    (M : Graph V) (hM : Matching M) (H : SimpleGraph (V×Fin W))
    [DecidableRel H.Adj] (hH : H≤unfolding G w W)
    (κ L : ℕ) (hk : 1≤κ) (hL : 1≤L) (n δ : ℝ)
    (hn : 2≤n) (hcard : (Fintype.card (V×Fin W) : ℝ)≤n) (hδ : 0<δ) (hδ1 : δ<1)
    (hlog : Real.log (100*n/δ)≤L)
    (hupper : ∀ x y,H.Adj x y→(H.degree x : ℝ)+H.degree y≤beta0 κ L) : V→Bool :=
  side M hM (canonicalOrientation M hM H Prod.fst
    (unfolding_original_ne G w W H hH)
    (unfolding_neighbor_parent_injective G w W H hH)
    κ L hk hL n δ hn hcard hδ hδ1 hlog hupper)

/-- Complete canonical unfolding-to-balanced-cut interface, with no
assumed concentration or balance event. N is restricted by this same cut;
the underfull classifier is not recomputed after restriction. -/
theorem canonical_unfolded_cut (G : SimpleGraph V) (w : Sym2 V→ℕ) (W : ℕ)
    (M : Graph V) (hM : Matching M) (H N : SimpleGraph (V×Fin W))
    [DecidableRel H.Adj] (hH : H≤unfolding G w W)
    (κ L : ℕ) (hk : 1≤κ) (hL : 1≤L) (n δ : ℝ)
    (hn : 2≤n) (hcard : (Fintype.card (V×Fin W) : ℝ)≤n) (hδ : 0<δ) (hδ1 : δ<1)
    (hlog : Real.log (100*n/δ)≤L)
    (hupper : ∀ x y,H.Adj x y→(H.degree x : ℝ)+H.degree y≤beta0 κ L)
    (hlower : ∀ x y,N.Adj x y→(1-1/10^9:ℝ)*beta0 κ L≤(H.degree x : ℝ)+H.degree y) :
    let z := canonicalCopySide G w W M hM H hH κ L hk hL n δ hn hcard hδ hδ1 hlog hupper
    (∀ e∈M,∀ u∈e.val,∀ v∈e.val,u≠v→z u≠z v) ∧
    (∀ x,(H.degree x : ℝ)/2-tolerance*beta0 κ L≤
        ((cutGraph H (fun y=>z y.1)).degree x : ℝ) ∧
      ((cutGraph H (fun y=>z y.1)).degree x : ℝ)≤
        (H.degree x : ℝ)/2+tolerance*beta0 κ L+1/2) ∧
    (∀ x y,(cutGraph H (fun y=>z y.1)).Adj x y→
      ((cutGraph H (fun y=>z y.1)).degree x : ℝ)+
        (cutGraph H (fun y=>z y.1)).degree y≤betaCut (beta0 κ L)) ∧
    (∀ x y,(cutGraph N (fun y=>z y.1)).Adj x y→
      (1-1/10^8:ℝ)*betaCut (beta0 κ L)≤
        ((cutGraph H (fun y=>z y.1)).degree x : ℝ)+
          (cutGraph H (fun y=>z y.1)).degree y) := by
  let ω := canonicalOrientation M hM H Prod.fst
    (unfolding_original_ne G w W H hH)
    (unfolding_neighbor_parent_injective G w W H hH)
    κ L hk hL n δ hn hcard hδ hδ1 hlog hupper
  have hb : Balanced M hM H Prod.fst (beta0 κ L) ω :=
    canonicalOrientation_balanced M hM H Prod.fst
      (unfolding_original_ne G w W H hH)
      (unfolding_neighbor_parent_injective G w W H hH)
      κ L hk hL n δ hn hcard hδ hδ1 hlog hupper
  have hi := cut_degree_interface H N (fun y=>side M hM ω y.1)
    (beta0_large κ L hk hL) hupper hlower hb
  refine ⟨?_,hb,hi.1,hi.2⟩
  intro e he u hu v hv hne
  exact benchmark_crosses M hM ω e he u v hu hv hne

theorem final_betaCut_integral (κ L : ℕ) :
    betaCut (beta0 κ L) =
      ((((5*10^29+2*10^20)*κ*L+1 : ℕ)) : ℝ) := by
  simp only [betaCut,beta0,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  ring

theorem final_betaCut_half_le (κ L : ℕ) :
    beta0 κ L/2≤betaCut (beta0 κ L) := by
  unfold betaCut beta0
  have h0 : (0:ℝ)≤(10^30:ℝ)*(κ:ℝ)*L := by positivity
  nlinarith

end RobustMatching.R8BalancedCut
