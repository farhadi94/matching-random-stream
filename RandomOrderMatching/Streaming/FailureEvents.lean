import RandomOrderMatching.Streaming.FullBufferExact
import RandomOrderMatching.Streaming.AbortProjection
import RandomOrderMatching.Streaming.SuffixOutput
import RandomOrderMatching.Streaming.SelectedFreeze
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Weights.Windows
open RandomOrderMatching.Phases.Execution RandomOrderMatching.Phases.WeightedState RandomOrderMatching.Graph.WeightedMatching
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def physicalSuffixValue (w : Edge V → ℕ) (cfg : Config) (model : BatchModel (Edge V) C)
    (l : List (Edge V)) : ℝ :=
  let tau := (run cfg model.copies l).freezeAt.getD l.length
  let view := acquisitionFrozenView cfg model (run cfg model.copies (l.take tau))
  ∑ e ∈ outputMatching w view.reference view.eligible (l.drop tau)
    (reachedCuts (l.drop tau).length),(w e:ℝ)

/-- Operational domination needs only actual final non-abort. The freeze is
proved from the potential, rather than supplied as a successful-phase premise. -/
theorem configured_output_dominates_physicalSuffix (w : Edge V → ℕ)
    (beta lower LU L0 : ℕ) (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : BatchModel (Edge V) C) (l : List (Edge V)) (hnd : l.Nodup)
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0 < l.length) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q
      (chosenScale l.length) hb hl
    (run cfg model.copies l).aborted=false →
      physicalSuffixValue w cfg model l ≤
        ∑ e ∈ configuredBoundedOutput w beta lower LU L0 hb hl model l,(w e:ℝ) := by
  dsimp only
  intro hs
  let Q := acquisitionBudget (Fintype.card C) beta
  let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q
    (chosenScale l.length) hb hl
  obtain ⟨tau,ht,hbound⟩ := configured_selected_acquisition_freezes beta lower LU L0 hb hl model l hnd hlarge
  have hm : 0 < l.length := (Nat.zero_le _).trans_lt hlarge
  let d := l.get ⟨0,hm⟩
  have he := configured_nonexact_suffix_output w beta lower LU L0 hb hl model l hnd d tau hlarge ht
    (fun i _ => acquisition_prefix_safe cfg model.copies l hs i)
  rw [he]
  unfold physicalSuffixValue
  rw [ht]
  simp only [Option.getD_some]
  rw [show (∑ e ∈ outputMatching w _ _ _ _,(w e:ℝ))=opt (fun e => (w e:ℝ))
    (bankSupport w _ _ _ _) from decode_real_weight w _]
  exact suffixOutput_dominates_bank w _ _ _

/-- The only possible losses are actual cap overflow, fixed-optimum prefix
loss, and the physical suffix theorem. This event inclusion contains the final
algorithm's output, and preserves the off-bracket analytic-score boundary. -/
theorem configured_failure_inclusion (w : Edge V → ℕ)
    (beta lower LU L0 : ℕ) (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : BatchModel (Edge V) C) (l : List (Edge V)) (hnd : l.Nodup)
    (hlarge : fullCapacity (Fintype.card V)
      (acquisitionBudget (Fintype.card C) beta) model.kappa L0 < l.length)
    (M : Graph V) (r : ℝ) (hr : 0 ≤ r) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q
      (chosenScale l.length) hb hl
    (∑ e ∈ configuredBoundedOutput w beta lower LU L0 hb hl model l,(w e:ℝ)) <
        r*(1-2*(1/100000000:ℝ))*(∑ e ∈ M,(w e:ℝ)) →
      (run cfg model.copies l).aborted=true ∨
      (∑ e ∈ survivingFixedMatching cfg model l M,(w e:ℝ)) <
        (1-2*(1/100000000:ℝ))*(∑ e ∈ M,(w e:ℝ)) ∨
      physicalSuffixValue w cfg model l <
        r*(∑ e ∈ survivingFixedMatching cfg model l M,(w e:ℝ)) := by
  dsimp only
  intro hbad
  let Q := acquisitionBudget (Fintype.card C) beta
  let cfg := configForScale beta lower (copiedCapacity Q model.kappa LU) Q
    (chosenScale l.length) hb hl
  by_cases ha : (run cfg model.copies l).aborted=true
  · exact Or.inl ha
  right
  by_cases hp : (∑ e ∈ survivingFixedMatching cfg model l M,(w e:ℝ)) <
      (1-2*(1/100000000:ℝ))*(∑ e ∈ M,(w e:ℝ))
  · exact Or.inl hp
  right
  by_contra hphase
  have hs : (run cfg model.copies l).aborted=false := Bool.eq_false_iff.mpr ha
  have hd := configured_output_dominates_physicalSuffix w beta lower LU L0 hb hl model l hnd hlarge hs
  have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hp) hr
  have hh := le_of_not_gt hphase
  nlinarith

/-- For a nonnegative ratio, success against all matching benchmarks is
exactly success against the attained original optimum. -/
theorem machine_good_iff_opt (a : Machine V) (alpha : ℝ) (ha : 0 ≤ alpha)
    (w : Edge V → ℕ) (l : List (Edge V)) :
    a.Good alpha w l ↔ alpha*opt (fun e => (w e:ℝ)) l.toFinset ≤
      ∑ e ∈ a.answer w l,(w e:ℝ) := by
  constructor
  · intro h
    have hh := h (decode w l.toFinset) (decode_subset w _) (decode_matching w _)
    rwa [decode_real_weight] at hh
  · intro h M hM hm
    have hb : (∑ e ∈ M,(w e:ℝ)) ≤ opt (fun e => (w e:ℝ)) l.toFinset := by
      rw [opt_eq_natOpt]
      exact_mod_cast matching_weight_le_natOpt w hM hm
    exact (mul_le_mul_of_nonneg_left hb ha).trans h

end RandomOrderMatching.Streaming
#print axioms RandomOrderMatching.Streaming.configured_failure_inclusion
#print axioms RandomOrderMatching.Streaming.machine_good_iff_opt
