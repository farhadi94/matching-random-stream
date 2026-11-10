import RandomOrderMatching.Streaming.Confidence
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Graph.WeightedMatching
open RandomOrderMatching.Phases.Execution
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def canonicalSelectedConfig (W L LU m : ℕ) (hW : 0 < W) (hL : 0 < L) : Config :=
  finalScaleConfig W L (canonicalBudget V W L)
    (copiedCapacity (canonicalBudget V W L) W LU) (chosenScale m) hW hL

theorem canonicalSelectedConfig_lower (W L LU m : ℕ) (hW : 0 < W) (hL : 0 < L) :
    (canonicalSelectedConfig (V:=V) W L LU m hW hL).lower=(10^30-10^21)*W*L := rfl

theorem canonicalSelectedConfig_beta (W L LU m : ℕ) (hW : 0 < W) (hL : 0 < L) :
    (canonicalSelectedConfig (V:=V) W L LU m hW hL).beta=10^30*W*L := rfl

theorem finalBoundedOutput_eq_configured (w : Edge V → ℕ) (W L LU L0 : ℕ)
    (hw : ∀ e,w e ≤ W) (hW : 0 < W) (hL : 0 < L) (h : Nonempty (Edge V))
    (l : List (Edge V)) :
    let seed := finalAcquisitionConfig W L 1 0 hW hL (by decide)
    finalBoundedOutput w W L LU L0 hw hW hL l=
      configuredBoundedOutput w seed.beta seed.lower LU L0 seed.beta_pos seed.lower_gap
        (canonicalBatchModel W w hw (Classical.choice h)) l := by
  unfold finalBoundedOutput
  rw [dif_pos h]
  rfl

/-- Canonical bounded-weight endpoint, with only the actual stopped-suffix
probability left as a premise. It is ready for the separately audited lift. -/
theorem canonical_failure_probability_of_suffix {m : ℕ} (hm : 0 < m)
    (W L LU L0 : ℕ) (hW : 0 < W) (hL : 0 < L)
    (label : Fin m → Edge V) (hi : Function.Injective label)
    (w : Edge V → ℕ) (hw : ∀ e,w e ≤ W)
    (hpos : ∀ e ∈ Finset.univ.image label,1 ≤ w e)
    (h : Nonempty (Edge V)) (r deltaSuffix : ℝ) (hr : 0 ≤ r)
    (hlarge : fullCapacity (Fintype.card V) (canonicalBudget V W L) W L0 < m) :
    let model := canonicalBatchModel W w hw (Classical.choice h)
    let cfg := canonicalSelectedConfig (V:=V) W L LU m hW hL
    let M := decode w (Finset.univ.image label)
    (((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      physicalSuffixValue w cfg model (labelledStream label pi) <
        r*(∑ e ∈ survivingFixedMatching cfg model (labelledStream label pi) M,(w e:ℝ)))).card:ℝ)/
      Fintype.card (Equiv.Perm (Fin m)) ≤ deltaSuffix) →
    ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ finalBoundedOutput w W L LU L0 hw hW hL (labelledStream label pi),(w e:ℝ)) <
        r*(1-2*(1/100000000:ℝ))*opt (fun e => (w e:ℝ)) (Finset.univ.image label))).card:ℝ)/
      Fintype.card (Equiv.Perm (Fin m)) ≤
      (canonicalBudget V W L:ℝ)*Real.exp (-(LU:ℝ))+Real.exp (-(L0:ℝ))+deltaSuffix := by
  dsimp only
  intro hs
  let seed := finalAcquisitionConfig W L 1 0 hW hL (by decide)
  let model := canonicalBatchModel W w hw (Classical.choice h)
  have hh := configured_failure_probability_of_suffix hm seed.beta seed.lower LU L0
    seed.beta_pos seed.lower_gap model label hi w hW
    (fun e he => ⟨hpos e he,hw e⟩) (decode w (Finset.univ.image label))
    (decode_subset w _) (decode_real_weight w _) r deltaSuffix hr hlarge hs
  have he : (Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ finalBoundedOutput w W L LU L0 hw hW hL (labelledStream label pi),(w e:ℝ)) <
        r*(1-2*(1/100000000:ℝ))*opt (fun e => (w e:ℝ)) (Finset.univ.image label))) =
    Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ configuredBoundedOutput w seed.beta seed.lower LU L0 seed.beta_pos seed.lower_gap
        model (labelledStream label pi),(w e:ℝ)) <
        r*(1-2*(1/100000000:ℝ))*opt (fun e => (w e:ℝ)) (Finset.univ.image label)) := by
    apply Finset.filter_congr
    intro pi _
    rw [finalBoundedOutput_eq_configured w W L LU L0 hw hW hL h]
  rw [he]
  exact hh

end RandomOrderMatching.Streaming
#print axioms RandomOrderMatching.Streaming.canonical_failure_probability_of_suffix
