import RandomOrderMatching.Streaming.FailureEvents
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Graph.WeightedMatching
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem failure_fraction_union {A : Type*} [Fintype A] (F X Y Z : A → Prop)
    (h : ∀ a,F a → X a ∨ Y a ∨ Z a) (dx dy dz : ℝ)
    (hx : ((Finset.univ.filter X).card:ℝ)/Fintype.card A ≤ dx)
    (hy : ((Finset.univ.filter Y).card:ℝ)/Fintype.card A ≤ dy)
    (hz : ((Finset.univ.filter Z).card:ℝ)/Fintype.card A ≤ dz) :
    ((Finset.univ.filter F).card:ℝ)/Fintype.card A ≤ dx+dy+dz := by
  have hs : Finset.univ.filter F ⊆
      (Finset.univ.filter X ∪ Finset.univ.filter Y) ∪ Finset.univ.filter Z := by
    intro a ha
    have hh := h a (Finset.mem_filter.mp ha).2
    simpa only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,or_assoc] using hh
  have hc : (Finset.univ.filter F).card ≤
      (Finset.univ.filter X).card+(Finset.univ.filter Y).card+(Finset.univ.filter Z).card :=
    (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hr : ((Finset.univ.filter F).card:ℝ) ≤
      (Finset.univ.filter X).card+(Finset.univ.filter Y).card+(Finset.univ.filter Z).card := by
    exact_mod_cast hc
  have hd := div_le_div_of_nonneg_right hr (Nat.cast_nonneg (Fintype.card A))
  rw [add_div,add_div] at hd
  linarith

/-- Complete wrapper composition conditional only on the actual physical
suffix event. Cap and fixed-optimum prefix bounds are discharged internally.
The remaining suffix premise is supplied by the stopped-history lift. -/
theorem configured_failure_probability_of_suffix {m : ℕ} (hm : 0 < m)
    (beta lower LU L0 : ℕ) (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : BatchModel (Edge V) C) (label : Fin m → Edge V) (hi : Function.Injective label)
    (w : Edge V → ℕ) (hk : 0 < model.kappa)
    (hw : ∀ e ∈ Finset.univ.image label,1 ≤ w e ∧ w e ≤ model.kappa)
    (M : Graph V) (hMG : M ⊆ Finset.univ.image label)
    (hopt : (∑ e ∈ M,(w e:ℝ))=opt (fun e => (w e:ℝ)) (Finset.univ.image label))
    (r deltaSuffix : ℝ) (hr : 0 ≤ r)
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0 < m) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q (chosenScale m) hb hl
    (((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      physicalSuffixValue w cfg model (labelledStream label pi) <
        r*(∑ e ∈ survivingFixedMatching cfg model (labelledStream label pi) M,(w e:ℝ)))).card:ℝ)/
      Fintype.card (Equiv.Perm (Fin m)) ≤ deltaSuffix) →
    ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ configuredBoundedOutput w beta lower LU L0 hb hl model (labelledStream label pi),(w e:ℝ)) <
        r*(1-2*(1/100000000:ℝ))*opt (fun e => (w e:ℝ)) (Finset.univ.image label))).card:ℝ)/
      Fintype.card (Equiv.Perm (Fin m)) ≤
      (Q:ℝ)*Real.exp (-(LU:ℝ))+Real.exp (-(L0:ℝ))+deltaSuffix := by
  dsimp only
  intro hphase
  let Q := acquisitionBudget (Fintype.card C) beta
  let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q (chosenScale m) hb hl
  refine failure_fraction_union _
    (fun pi => (run cfg model.copies (labelledStream label pi)).aborted=true)
    (fun pi => (∑ e ∈ survivingFixedMatching cfg model (labelledStream label pi) M,(w e:ℝ)) <
      (1-2*(1/100000000:ℝ))*opt (fun e => (w e:ℝ)) (Finset.univ.image label))
    (fun pi => physicalSuffixValue w cfg model (labelledStream label pi) <
      r*(∑ e ∈ survivingFixedMatching cfg model (labelledStream label pi) M,(w e:ℝ)))
    ?_ ((Q:ℝ)*Real.exp (-(LU:ℝ))) (Real.exp (-(L0:ℝ))) deltaSuffix ?_ ?_ ?_
  · intro pi hbad
    have hh := configured_failure_inclusion w beta lower LU L0 hb hl model
      (labelledStream label pi) (labelledStream_nodup label hi pi)
      (by simpa only [labelledStream_length] using hlarge) M r hr
    simp only [labelledStream_length,hopt] at hh
    exact hh hbad
  · simpa only [cfg,Q] using configured_cap_failure_probability hm beta lower LU L0 hb hl model label hi hlarge
  · exact configured_optimum_witness_failure hm beta lower LU L0 hb hl model label hi w hk hw M hMG hopt hlarge
  · exact hphase

theorem confidence_exp_bound {L x : ℝ} (hx : 0 < x) (hL : Real.log (1/x) ≤ L) :
    Real.exp (-L) ≤ x := by
  have hh : -L ≤ Real.log x := by rw [Real.log_div (by norm_num) (ne_of_gt hx),Real.log_one] at hL; linarith
  exact (Real.exp_le_exp.mpr hh).trans_eq (Real.exp_log hx)

theorem wrapper_confidence_budget {Q LU L0 delta : ℝ}
    (hQ : 0 < Q) (hd : 0 < delta)
    (h0 : Real.log (100/delta) ≤ L0) (hu : Real.log (100*Q/delta) ≤ LU) :
    Q*Real.exp (-LU)+Real.exp (-L0)+7*delta/100 ≤ delta := by
  have hzero := confidence_exp_bound (show 0 < delta/100 by positivity)
    (by convert h0 using 1 <;> congr 1 <;> field_simp : Real.log (1/(delta/100)) ≤ L0)
  have hupper := confidence_exp_bound (show 0 < delta/(100*Q) by positivity)
    (by convert hu using 1 <;> congr 1 <;> field_simp : Real.log (1/(delta/(100*Q))) ≤ LU)
  have hh := mul_le_mul_of_nonneg_left hupper hQ.le
  have he : Q*(delta/(100*Q))=delta/100 := by field_simp
  rw [he] at hh
  linarith

end RandomOrderMatching.Streaming
#print axioms RandomOrderMatching.Streaming.configured_failure_probability_of_suffix
#print axioms RandomOrderMatching.Streaming.wrapper_confidence_budget
