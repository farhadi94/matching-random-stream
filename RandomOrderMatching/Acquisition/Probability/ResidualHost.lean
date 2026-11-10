import RandomOrderMatching.Acquisition.Probability.StoppingTime
import RandomOrderMatching.Acquisition.Probability.PrefixLoss

/-! The physical original-edge host after the actual copied acquisition:
retained reference parents plus every original whose label is still unseen. -/
noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Graph.WeightedMatching
open RandomOrderMatching.Probability.Stopping
variable {V O : Type*} [Fintype V] [DecidableEq V] [DecidableEq O]

def originalHost {n : ℕ} (hn : 0<n) (cfg : Config) (model : BatchModel (Fin n) V)
    (label : Fin n → Edge O) (π : Equiv.Perm (Fin n)) : Graph O :=
  (actualReference hn cfg model.copies π (acquisitionStop hn cfg model.copies π)).image
      (fun e => label (model.parent e)) ∪
    (Finset.univ \ (positions (acquisitionStop hn cfg model.copies π)).image π).image label

theorem originalHost_contains_suffix {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (label : Fin n → Edge O)
    (π : Equiv.Perm (Fin n)) :
    Finset.univ.image label \
      ((positions (acquisitionStop hn cfg model.copies π)).image π).image label ⊆
        originalHost hn cfg model label π := by
  intro e he
  obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp he
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hin
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨a,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  intro hseen
  exact hout (Finset.mem_image_of_mem label hseen)

theorem originalHost_subset_input {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (label : Fin n → Edge O)
    (π : Equiv.Perm (Fin n)) : originalHost hn cfg model label π ⊆ Finset.univ.image label := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image_of_mem label (Finset.mem_univ _)
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image_of_mem label (Finset.mem_univ _)

/-- Conditioning on the actual stopping history fixes both the reference
parents and the entire unordered suffix host. Future repair outcomes are absent. -/
theorem originalHost_eq_on_stopped_history {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (label : Fin n → Edge O)
    (σ π : Equiv.Perm (Fin n))
    (hp : π ∈ stoppedCylinder (acquisitionStop hn cfg model.copies) σ) :
    originalHost hn cfg model label π=originalHost hn cfg model label σ := by
  rw [stoppedCylinder_eq _ (acquisitionStop_causal hn cfg model.copies) σ] at hp
  have hstop := stop_eq_on_cylinder _ (acquisitionStop_causal hn cfg model.copies) σ π hp
  have href := actualReference_prefix hn cfg model.copies _ (acquisitionStop_le hn cfg model.copies σ) σ π hp
  have hrem := remaining_eq_of_cylinder _ σ π hp
  unfold RandomOrderMatching.Probability.Permutation.remaining at hrem
  unfold originalHost
  rw [hstop,href,hrem]

/-- This is preservation of the actual physical host; the only execution
input is its deterministic enclosing-prefix bound, supplied by acquisition
progress and the chosen-scale arithmetic. No retained-value premise is assumed. -/
theorem actual_host_prefix_preservation {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (label : Fin n → Edge O) (hi : Function.Injective label)
    (w : Edge O → ℕ) (k : ℕ) (hk : k≤n) (W ρ : ℝ)
    (hW : 0<W) (hρ : 0≤ρ) (hw : ∀ e ∈ Finset.univ.image label,(w e : ℝ)≤W)
    (hs : (k : ℝ)/n≤ρ)
    (hstop : ∀ π,acquisitionStop hn cfg model.copies π≤k) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      opt (fun e => (w e : ℝ)) (originalHost hn cfg model label π) <
        (1-2*ρ)*opt (fun e => (w e : ℝ)) (Finset.univ.image label))).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin n)) ≤
        Real.exp (-ρ*opt (fun e => (w e : ℝ)) (Finset.univ.image label)/(3*W)) := by
  exact bounded_freeze_prefix_preservation label hi (Finset.univ.image label) rfl w k hk hn W ρ
    hW hρ hw hs (acquisitionStop hn cfg model.copies) hstop
    (originalHost hn cfg model label) (originalHost_contains_suffix hn cfg model label)

end RandomOrderMatching.Acquisition.Probability
