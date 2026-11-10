import RobustMatching.R8StreamingWrapperMain
noncomputable section
open Classical
open scoped BigOperators
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R8WeightWindows RobustMatching.R7ProbabilityRestriction
open RobustMatching.R6FableImportance
variable {V : Type*} [Fintype V] [LinearOrder V]
set_option maxHeartbeats 1000000

theorem confidentMachine_answer_global (W : ℕ) (delta : ℝ) (hW : 0 < W)
    (w : Edge V → ℕ) (hw : ∀ e,w e ≤ W) (l : List (Edge V)) :
    let L := confidenceLog (Fintype.card V) W delta
    let Q := canonicalBudget V W L
    (confidentMachine (V:=V) W delta hW).answer w l=
      finalBoundedOutput w W L (capLog (Fintype.card V) W Q delta) (prefixLog delta)
        hw hW (confidenceLog_pos _ _ _) l := by
  dsimp only [confidentMachine]
  rw [canonicalMachine_answer]
  unfold clampedBoundedOutput
  have he : clippedWeight w W=w := funext (fun e => clippedWeight_eq w W e (hw e))
  simp only [he]

theorem permMean_labelled_failure_fraction {m : ℕ} (label : Fin m → Edge V)
    (hi : Function.Injective label) (Good : List (Edge V) → Prop) :
    permMean (List.ofFn label) (fun u => if Good u then 0 else 1)=
      ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
        ¬Good (labelledStream label pi))).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)) := by
  rw [permMean_labelled label hi]
  congr 1
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro pi _
  split_ifs <;> simp_all

/-- Actual original-label permutation theorem for finalBoundedOutput, with
all confidence parameters fixed. This also covers m=0; only edges actually
present in the fixed input must have positive weight. -/
theorem finalBoundedOutput_uniform_probability {m : ℕ}
    (W : ℕ) (hW : 0 < W) (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (w : Edge V → ℕ) (hw : ∀ e,w e ≤ W)
    (label : Fin m → Edge V) (hi : Function.Injective label)
    (hpos : ∀ e ∈ Finset.univ.image label,1 ≤ w e) :
    let L := confidenceLog (Fintype.card V) W delta
    let Q := canonicalBudget V W L
    ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ finalBoundedOutput w W L (capLog (Fintype.card V) W Q delta) (prefixLog delta)
        hw hW (confidenceLog_pos _ _ _) (labelledStream label pi),(w e:ℝ)) <
      finalRatio*opt (fun e => (w e:ℝ)) (Finset.univ.image label))).card:ℝ)/
        Fintype.card (Equiv.Perm (Fin m)) ≤ delta := by
  have hh := bounded_integer_random_order W hW delta hd hd1 w (List.ofFn label)
    (List.nodup_ofFn.mpr hi) (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      exact ⟨hpos _ (Finset.mem_image_of_mem label (Finset.mem_univ _)),hw _⟩)
  rw [permMean_labelled_failure_fraction label hi] at hh
  have he : (Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      ¬(confidentMachine (V:=V) W delta hW).Good finalRatio w (labelledStream label pi))) =
      Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ (confidentMachine (V:=V) W delta hW).answer w (labelledStream label pi),(w e:ℝ)) <
      finalRatio*opt (fun e => (w e:ℝ)) (Finset.univ.image label)) := by
    apply Finset.filter_congr
    intro pi _
    rw [machine_good_iff_opt _ _ finalRatio_bounds.1,not_le,labelledStream_toFinset]
  rw [he] at hh
  simp only [confidentMachine_answer_global W delta hW w hw] at hh
  exact hh

end RobustMatching.R8StreamingWrapper
