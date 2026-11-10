import RandomOrderMatching.Analysis.Repair.Probability.LocalSums
import RandomOrderMatching.Analysis.Repair.Probability.RangeBounds

noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair.Probability
open RandomOrderMatching.Analysis.Repair RandomOrderMatching.Analysis.Repair.Typed
variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]

lemma normalizer_ge_third (sideO : Outsides R M G U→Bool) (layer : Bool)
    (x : Outsides R M G U) : (1:ℝ)/3≤normalizer alpha omega sideO layer x := by
  rcases x with r|m|g|u <;> unfold normalizer capacity <;>
    split_ifs <;> norm_num [primaryCap,secondaryCap,alpha,omega] at *

lemma inverse_normalizer_scale (sideO : Outsides R M G U→Bool) (layer : Bool)
    (x : Outsides R M G U) {v : ℝ} (hv : 0≤v) :
    v/normalizer alpha omega sideO layer x≤3*v := by
  have hp := normalizer_pos alpha omega parameters.1 parameters.2 sideO layer x
  apply (div_le_iff₀ hp).mpr
  nlinarith [normalizer_ge_third sideO layer x]

/-- Explicit local row square-range bound for the final capped weights.
The fiber hypothesis counts actual stochastic neighboring copies. -/
theorem row_square_budget
    (p : Parents B G M J R) (b0 : B)
    (H : Centers G M P I J→Outsides R M G U→Prop)
    (w : Centers G M P I J→Outsides R M G U→ℝ)
    (hw : ∀c x,0≤w c x) (hsupport : ∀c x,¬H c x→w c x=0)
    (hrow : ∀c,∑x,w c x≤1)
    (sideO : Outsides R M G U→Bool) (layer : Bool) (c : Centers G M P I J)
    {β : ℝ} (hβ : 0<β) (hweight : ∀c x,w c x≤100/β) (κ : ℕ)
    (hfiber : ∀b,(Finset.univ.filter fun x=>H c x ∧ outsideParent p b0 x=b ∧
      signalRange (receiverSignalAt sideO layer x)≠0).card≤2*κ) :
    ∑b,(blockRange (outsideParent p b0)
      (signalRanges (receiverSignalAt sideO layer)
        (fun x=>w c x/normalizer alpha omega sideO layer x)) b)^2 ≤1800*κ/β := by
  let a := fun x=>w c x/normalizer alpha omega sideO layer x
  let s := receiverSignalAt sideO layer
  have ha : ∀x,0≤a x := fun x=>div_nonneg (hw c x)
    (le_of_lt (normalizer_pos alpha omega parameters.1 parameters.2 sideO layer x))
  have hc (b) : (Finset.univ.filter fun x=>outsideParent p b0 x=b ∧ signalRanges s a x≠0).card≤2*κ := by
    refine (Finset.card_le_card ?_).trans (hfiber b)
    intro x hx
    obtain ⟨_,hp,hr⟩ := Finset.mem_filter.mp hx
    have hwa : w c x≠0 := by intro hz; exact hr (by simp [signalRanges,a,hz])
    have hs : signalRange (s x)≠0 := by intro hz; exact hr (by simp [signalRanges,hz])
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,⟨by by_contra hh;exact hwa (hsupport c x hh),hp,hs⟩⟩
  have hamax (x) : a x≤300/β := by
    have h1 := inverse_normalizer_scale sideO layer x (hw c x)
    have h2 := hweight c x
    calc
      a x ≤ 3*w c x := h1
      _ ≤ 3*(100/β) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 300/β := by ring
  have hsum : ∑x,signalRanges s a x≤3 := by
    calc
      _ ≤ ∑x,a x := Finset.sum_le_sum fun x _=>signalRanges_le s a ha x
      _ ≤ ∑x,3*w c x := Finset.sum_le_sum fun x _=>inverse_normalizer_scale sideO layer x (hw c x)
      _ = 3*(∑x,w c x) := by rw [Finset.mul_sum]
      _ ≤ 3 := by linarith [hrow c]
  have h := batch_support_square_budget (outsideParent p b0) (signalRanges s a) (2*κ) hc
    (signalRanges_nonneg s a ha) (by positivity : (0:ℝ)≤300/β)
    (fun x=>(signalRanges_le s a ha x).trans (hamax x)) hsum
  convert h using 1 <;> push_cast <;> ring

/-- The column tolerance is scaled by its capped degree denominator d. -/
theorem column_square_budget
    (p : Parents B G M J R) (b0 : B)
    (H : Centers G M P I J→Outsides R M G U→Prop)
    (w : Centers G M P I J→Outsides R M G U→ℝ)
    (hw : ∀c x,0≤w c x) (hsupport : ∀c x,¬H c x→w c x=0)
    (sideO : Outsides R M G U→Bool) (layer : Bool) (x : Outsides R M G U)
    {β d : ℝ} (hβ : 0<β) (hd : 0<d)
    (hweight : ∀c,w c x≤1/(β*d)) (hmass : ∑c,w c x≤1/d) (κ : ℕ)
    (hfiber : ∀b,(Finset.univ.filter fun c=>H c x ∧ centerParent p b0 c=b ∧
      signalRange (senderSignalAt sideO layer x c)≠0).card≤2*κ) :
    ∑b,(blockRange (centerParent p b0)
      (signalRanges (senderSignalAt sideO layer x) (fun c=>w c x)) b)^2 ≤2*κ/(β*d^2) := by
  let s : Centers G M P I J→Signal := senderSignalAt sideO layer x
  let a := fun c=>w c x
  have ha : ∀c,0≤a c := fun c=>hw c x
  have hc (b) : (Finset.univ.filter fun c=>centerParent p b0 c=b ∧ signalRanges s a c≠0).card≤2*κ := by
    refine (Finset.card_le_card ?_).trans (hfiber b)
    intro c hc
    obtain ⟨_,hp,hr⟩ := Finset.mem_filter.mp hc
    have hwc : w c x≠0 := by intro hz;exact hr (by simp [signalRanges,a,hz])
    have hs : signalRange (s c)≠0 := by intro hz;exact hr (by simp [signalRanges,hz])
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ c,⟨by by_contra hh;exact hwc (hsupport c x hh),hp,hs⟩⟩
  have hsum : ∑c,signalRanges s a c≤1/d :=
    (Finset.sum_le_sum fun c _=>signalRanges_le s a ha c).trans hmass
  have h := batch_support_square_budget (centerParent p b0) (signalRanges s a) (2*κ) hc
    (signalRanges_nonneg s a ha) (by positivity : (0:ℝ)≤1/(β*d))
    (fun c=>(signalRanges_le s a ha c).trans (hweight c)) hsum
  convert h using 1 <;> push_cast <;> ring

end RandomOrderMatching.Analysis.Repair.Probability
