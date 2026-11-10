import RobustMatching.R8StreamingWrapperContract
import RobustMatching.R7ReductionCertificate
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R8Acquisition RobustMatching.R6FableImportance
open RobustMatching.R7WeightedPhaseAssembly
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def suffixRatio : ℝ := (R7ReductionCertificate.Concrete.target:ℝ)-1/10000000
def finalRatio : ℝ := 71295/100000

theorem suffixRatio_pos : 0 < suffixRatio := by
  norm_num [suffixRatio,R7ReductionCertificate.Concrete.target]
theorem finalRatio_bounds : 0 ≤ finalRatio ∧ finalRatio ≤ 1 := by norm_num [finalRatio]
theorem finalRatio_le_preserved : finalRatio ≤ suffixRatio*(1-2*(1/100000000:ℝ)) := by
  norm_num [finalRatio,suffixRatio,R7ReductionCertificate.Concrete.target]

theorem failure_fraction_mono {A : Type*} [Fintype A] (F G : A → Prop)
    (h : ∀ a,F a → G a) :
    ((Finset.univ.filter F).card:ℝ)/Fintype.card A ≤
      ((Finset.univ.filter G).card:ℝ)/Fintype.card A := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h a (Finset.mem_filter.mp ha).2⟩

/-- Instantiate all integer confidence choices, clamp-domain handling and
exact/full branches. Its sole remaining input is the actual stopped-suffix
lift, which is proved separately from the acquisition and fixed-host packets. -/
theorem confidentMachine_contract_of_suffix_lift (W : ℕ) (hW : 0 < W)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (hs : ∀ {m : ℕ}, 0 < m → (w : Edge V → ℕ) → (hw : ∀ e,w e ≤ W) →
      (label : Fin m → Edge V) → Function.Injective label →
      (h : Nonempty (Edge V)) →
      let L := confidenceLog (Fintype.card V) W delta
      let Q := canonicalBudget V W L
      let LU := capLog (Fintype.card V) W Q delta
      let model := canonicalBatchModel W w hw (Classical.choice h)
      let cfg := canonicalSelectedConfig (V:=V) W L LU m hW (confidenceLog_pos _ _ _)
      let M := decode w (Finset.univ.image label)
      fullCapacity (Fintype.card V) Q W (prefixLog delta) < m →
      ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
        physicalSuffixValue w cfg model (labelledStream label pi) <
          suffixRatio*(∑ e ∈ survivingFixedMatching cfg model (labelledStream label pi) M,(w e:ℝ)))).card:ℝ)/
        Fintype.card (Equiv.Perm (Fin m)) ≤ 7*delta/100) :
    (confidentMachine (V:=V) W delta hW).Contract W finalRatio delta := by
  let L := confidenceLog (Fintype.card V) W delta
  let Q := canonicalBudget V W L
  let LU := capLog (Fintype.card V) W Q delta
  let L0 := prefixLog delta
  have hL : 0 < L := confidenceLog_pos _ _ _
  apply canonicalMachine_contract_of_uniform_nonexact W L LU L0 hW hL finalRatio delta
    finalRatio_bounds.1 finalRatio_bounds.2 hd.le
  intro m hm w hw label hi hpos hlarge
  let h : Nonempty (Edge V) := ⟨label ⟨0,hm⟩⟩
  have hsuffix := hs hm w hw label hi h hlarge
  have hh := canonical_failure_probability_of_suffix hm W L LU L0 hW hL label hi w hw hpos h
    suffixRatio (7*delta/100) suffixRatio_pos.le hlarge hsuffix
  have hQ : 0 < Q := by dsimp [Q,canonicalBudget,acquisitionBudget]; omega
  have hbudget := actual_confidence_budget (Fintype.card V) W Q hQ hd hd1
  apply le_trans _ (hh.trans hbudget)
  apply failure_fraction_mono
  intro pi hp
  have hopt : 0 ≤ opt (fun e => (w e:ℝ)) (Finset.univ.image label) := by
    rw [R7WeightedPhase.opt_eq_natOpt]
    positivity
  have hr := mul_le_mul_of_nonneg_right finalRatio_le_preserved hopt
  exact hp.trans_le hr

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.confidentMachine_contract_of_suffix_lift
