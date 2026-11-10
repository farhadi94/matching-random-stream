import RobustMatching.R8AcquisitionCollect
import RobustMatching.R8AcquisitionProvenance

noncomputable section
open Classical
namespace RobustMatching.R8Acquisition
open RobustMatching.R2Cut
variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- A surviving frozen step retains the complete old store and every eligible copied arrival. -/
theorem frozen_step_surviving (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (a : E) (hf : s.freezeAt≠none)
    (ha : (step cfg batch s a).aborted=false) :
    step cfg batch s a={s with time:=s.time+1, saved:=s.saved ∪ underfullRecords cfg.lower s.ref (batch a) (s.time+1)} := by
  cases hs : s.aborted with
  | true => simp [step,hs] at ha
  | false =>
    by_cases hc : (s.saved ∪ underfullRecords cfg.lower s.ref (batch a) (s.time+1)).card≤cfg.uCap
    · simpa only [hs] using frozen_step_complete cfg batch s a hf hs hc
    · simp [step,hs,hf,collectStep,hc] at ha

theorem frozen_step_saved_mono (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (a : E) (hf : s.freezeAt≠none)
    (ha : (step cfg batch s a).aborted=false) : s.saved⊆(step cfg batch s a).saved := by
  rw [frozen_step_surviving cfg batch s a hf ha]
  exact Finset.subset_union_left

theorem frozen_step_retains_copy (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (a : E) (hf : s.freezeAt≠none)
    (ha : (step cfg batch s a).aborted=false) {e : Edge V}
    (he : e∈batch a) (hd : edgeDegree s.ref e<cfg.lower) :
    (e,s.time+1)∈(step cfg batch s a).saved := by
  rw [frozen_step_surviving cfg batch s a hf ha]
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he,hd⟩,rfl⟩

theorem recordsFrom_contains (lower : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (t : ℕ) (as : List E) {a : E} (ha : a∈as) {e : Edge V}
    (he : e∈batch a) (hd : edgeDegree H e<lower) :
    ∃ stamp,(e,stamp)∈recordsFrom lower H batch t as := by
  induction as generalizing t with
  | nil => simp at ha
  | cons b as ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst b
      refine ⟨t+1,Finset.mem_union_left _ ?_⟩
      exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he,hd⟩,rfl⟩
    · obtain ⟨stamp,hstamp⟩ := ih (t+1) h
      exact ⟨stamp,Finset.mem_union_right _ hstamp⟩

theorem frozen_parent_retained [DecidableEq E] (cfg : Config) (model : BatchModel E V)
    (s : State V) (as : List E) (hf : s.freezeAt≠none) (habort : s.aborted=false)
    (hc : (s.saved ∪ recordsFrom cfg.lower s.ref model.copies s.time as).card≤cfg.uCap)
    {a : E} (ha : a∈as) {e : Edge V} (he : e∈model.copies a) (hd : edgeDegree s.ref e<cfg.lower) :
    ∃ stamp,(a,stamp)∈savedParents model.parent (runFrom cfg model.copies s as) := by
  obtain ⟨stamp,hstamp⟩ := recordsFrom_contains cfg.lower s.ref model.copies s.time as ha he hd
  refine ⟨stamp,?_⟩
  rw [frozen_run_complete cfg model.copies s as hf habort hc]
  apply Finset.mem_image.mpr
  refine ⟨(e,stamp),Finset.mem_union_right _ hstamp,?_⟩
  simp [model.parent_mem a e he]

end RobustMatching.R8Acquisition
#print axioms RobustMatching.R8Acquisition.frozen_step_retains_copy
#print axioms RobustMatching.R8Acquisition.frozen_parent_retained
