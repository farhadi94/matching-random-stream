import RandomOrderMatching.Analysis.Repair.Probability.LocalRanges

/-! The advertised common local tail, derived from actual events and
original-block square ranges, including zero-variance neighborhoods. -/
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair.Probability
open RandomOrderMatching.Analysis.Repair RandomOrderMatching.Analysis.Repair.Typed
variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]

theorem row_failure_bound
    (p : Parents B G M J R) (b0 : B)
    (H : Centers G M P I J→Outsides R M G U→Prop)
    (sideC : Centers G M P I J→Bool) (sideO : Outsides R M G U→Bool)
    (hcross : ∀c x,H c x→sideC c≠sideO x)
    (w : Centers G M P I J→Outsides R M G U→ℝ)
    (hw : ∀c x,0≤w c x) (hsupport : ∀c x,¬H c x→w c x=0)
    (hrow : ∀c,∑x,w c x≤1)
    (layer : Bool) (c : Centers G M P I J)
    {β ε : ℝ} (hβ : 0<β) (hε : 0<ε) (hweight : ∀c x,w c x≤100/β)
    (κ : ℕ) (hκ : 0<κ)
    (hfiber : ∀b,(Finset.univ.filter fun x=>H c x ∧ outsideParent p b0 x=b ∧
      signalRange (receiverSignalAt sideO layer x)≠0).card≤2*κ) :
    (experiment (B:=B)).real {z | 1+ε<rowLoad
      (rawSupport (states p z) H sideC sideO w (normalizer alpha omega sideO) layer) c} ≤
      Real.exp (-ε^2*β/(4000*κ)) := by
  have hk : (0:ℝ)<κ := Nat.cast_pos.mpr hκ
  have hb := row_square_budget p b0 H w hw hsupport hrow sideO layer c hβ hweight κ hfiber
  have hbig : 1800*(κ:ℝ)/β≤8000*κ/β := by apply div_le_div_of_nonneg_right _ (le_of_lt hβ);nlinarith
  have ha : ∀x,0≤w c x/normalizer alpha omega sideO layer x := fun x=>div_nonneg (hw c x)
    (le_of_lt (normalizer_pos alpha omega parameters.1 parameters.2 sideO layer x))
  have ht := signal_upper_tail_budget (outsideParent p b0) (receiverSignalAt sideO layer)
    (fun x=>w c x/normalizer alpha omega sideO layer x) ha hε
    (by positivity : (0:ℝ)<8000*κ/β) (hb.trans hbig)
  have heq : -2*ε^2/(8000*(κ:ℝ)/β)= -ε^2*β/(4000*κ) := by
    field_simp
    ring
  rw [heq] at ht
  refine (measureReal_mono ?_).trans ht
  intro z hz
  change 1+ε<rowLoad (rawSupport (states p z) H sideC sideO w (normalizer alpha omega sideO) layer) c at hz
  change ε≤signalSum _ _ _ z-signalExpectation _ _
  have h1 := row_dominated p b0 z H sideC sideO hcross w hw layer c
  have h2 := (receiverExpectation_le w hw sideO layer c).trans (hrow c)
  linarith

lemma live_column_tolerance (p : Parents B G M J R) (z : B→Clock)
    (sideO : Outsides R M G U→Bool) (layer : Bool) (x : Outsides R M G U)
    (hlive : liveReceiver (states p z) sideO layer x)
    {d ε : ℝ} (hd : (1:ℝ)/100≤d) (hε : 0≤ε) :
    (ε/d)/capacity alpha omega sideO layer x≤300*ε := by
  have hdp : 0<d := by linarith
  have hp := live_capacity_pos (states p z) alpha omega parameters.1 parameters.2 sideO layer x hlive
  have hthird := normalizer_ge_third sideO layer x
  simp only [normalizer,if_neg (ne_of_gt hp)] at hthird
  have h1 : ε/d≤100*ε := by apply (div_le_iff₀ hdp).mpr;nlinarith
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem column_failure_bound
    (p : Parents B G M J R) (b0 : B)
    (H : Centers G M P I J→Outsides R M G U→Prop)
    (sideC : Centers G M P I J→Bool) (sideO : Outsides R M G U→Bool)
    (hcross : ∀c x,H c x→sideC c≠sideO x)
    (w : Centers G M P I J→Outsides R M G U→ℝ)
    (hw : ∀c x,0≤w c x) (hsupport : ∀c x,¬H c x→w c x=0)
    (layer : Bool) (x : Outsides R M G U)
    {β d ε : ℝ} (hβ : 0<β) (hd : (1:ℝ)/100≤d) (hε : 0<ε)
    (hweight : ∀c,w c x≤1/(β*d)) (hmass : ∑c,w c x≤1/d)
    (κ : ℕ) (hκ : 0<κ)
    (hfiber : ∀b,(Finset.univ.filter fun c=>H c x ∧ centerParent p b0 c=b ∧
      signalRange (senderSignalAt sideO layer x c)≠0).card≤2*κ) :
    (experiment (B:=B)).real {z | liveReceiver (states p z) sideO layer x ∧
      colLoad (rawSupport (states p z) H sideC sideO w (normalizer alpha omega sideO) layer) x <
        meanLoad alpha omega w sideO layer x/capacity alpha omega sideO layer x-300*ε} ≤
      Real.exp (-ε^2*β/(4000*κ)) := by
  have hk : (0:ℝ)<κ := Nat.cast_pos.mpr hκ
  have hdp : 0<d := by linarith
  have hb := column_square_budget p b0 H w hw hsupport sideO layer x hβ hdp hweight hmass κ hfiber
  have hbig : 2*(κ:ℝ)/(β*d^2)≤8000*κ/(β*d^2) := by
    apply div_le_div_of_nonneg_right _ (by positivity);nlinarith
  have ht := signal_lower_tail_budget (centerParent p b0) (senderSignalAt sideO layer x)
    (fun c=>w c x) (fun c=>hw c x) (div_pos hε hdp)
    (by positivity : (0:ℝ)<8000*κ/(β*d^2)) (hb.trans hbig)
  have heq : -2*(ε/d)^2/(8000*(κ:ℝ)/(β*d^2))= -ε^2*β/(4000*κ) := by
    field_simp
    ring
  rw [heq] at ht
  refine (measureReal_mono ?_).trans ht
  rintro z ⟨hlive,hz⟩
  rw [live_column_eq p b0 z H sideC sideO hcross w hsupport layer x hlive] at hz
  have hp := live_capacity_pos (states p z) alpha omega parameters.1 parameters.2 sideO layer x hlive
  have herr := live_column_tolerance p z sideO layer x hlive hd (le_of_lt hε)
  have hlt : signalSum (centerParent p b0) (senderSignalAt sideO layer x) (fun c=>w c x) z /
      capacity alpha omega sideO layer x <
      (meanLoad alpha omega w sideO layer x-ε/d)/capacity alpha omega sideO layer x := by
    rw [sub_div]
    linarith
  have hh := (div_lt_div_iff_of_pos_right hp).mp hlt
  change ε/d≤signalExpectation _ _-signalSum _ _ _ z
  rw [senderExpectation_eq]
  linarith

end RandomOrderMatching.Analysis.Repair.Probability
