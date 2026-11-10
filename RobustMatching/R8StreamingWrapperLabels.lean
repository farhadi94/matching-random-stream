import RobustMatching.R8AcquisitionProbabilityParents
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R8Acquisition
open RobustMatching.R8AcquisitionProbability RobustMatching.R7ProbabilityPermutation
variable {C E L : Type*} [Fintype C] [DecidableEq C]
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

def labelledParent [Nonempty L] (model : BatchModel E C) (label : L→E) (e : Edge C) : L :=
  if h : ∃i,label i=model.parent e then Classical.choose h else Classical.choice inferInstance

def labelledModel [Nonempty L] (model : BatchModel E C) (label : L→E)
    (hi : Function.Injective label) : BatchModel L C where
  copies i := model.copies (label i)
  parent := labelledParent model label
  kappa := model.kappa
  parent_mem i e he := by
    have hp := model.parent_mem (label i) e he
    have hex : ∃j,label j=model.parent e := ⟨i,hp.symm⟩
    unfold labelledParent
    rw [dif_pos hex]
    apply hi
    exact (Classical.choose_spec hex).trans hp
  nodup i := model.nodup (label i)
  batch_bound i := model.batch_bound (label i)

theorem acquisition_run_map (cfg : Config) (batch : E→List (Edge C))
    (label : L→E) (l : List L) :
    run cfg batch (l.map label)=run cfg (fun i => batch (label i)) l := by
  unfold run runFrom
  rw [List.foldl_map]
  rfl

def labelledStream {m : ℕ} (label : Fin m→E) (pi : Equiv.Perm (Fin m)) : List E :=
  (List.ofFn pi).map label

theorem labelledStream_length {m : ℕ} (label : Fin m→E) (pi : Equiv.Perm (Fin m)) :
    (labelledStream label pi).length=m := by simp [labelledStream]

theorem labelledStream_nodup {m : ℕ} (label : Fin m→E) (hi : Function.Injective label)
    (pi : Equiv.Perm (Fin m)) : (labelledStream label pi).Nodup := by
  exact (List.nodup_ofFn.mpr pi.injective).map hi

theorem labelled_final_state {m : ℕ} (hm : 0 < m) (cfg : Config)
    (batch : E→List (Edge C)) (label : Fin m→E) (pi : Equiv.Perm (Fin m)) :
    run cfg batch (labelledStream label pi)=
      stateAt cfg (fun i => batch (label i)) (permutationStream hm pi) m := by
  rw [stateAt,permutation_inputPrefix hm pi m le_rfl]
  rw [List.take_of_length_le (by simp : (List.ofFn pi).length ≤ m)]
  exact acquisition_run_map cfg batch label (List.ofFn pi)


end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.acquisition_run_map
