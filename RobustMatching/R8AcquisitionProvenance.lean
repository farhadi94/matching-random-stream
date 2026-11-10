import RobustMatching.R8AcquisitionStateBasic

noncomputable section
open Classical
namespace RobustMatching.R8Acquisition
open RobustMatching.R2Cut
variable {V E : Type*} [Fintype V] [DecidableEq V]

theorem seenCopies_cons (batch : E → List (Edge V)) (a : E) (as : List E) :
    seenCopies batch (a::as)=(batch a).toFinset ∪ seenCopies batch as := by
  simp [seenCopies]

theorem runFrom_ref_subset (cfg : Config) (batch : E → List (Edge V))
    (s : State V) (as : List E) :
    (runFrom cfg batch s as).ref ⊆ s.ref ∪ seenCopies batch as := by
  induction as generalizing s with
  | nil => simp [runFrom,seenCopies]
  | cons a as ih =>
    intro e he
    have hh := ih (step cfg batch s a) he
    rcases Finset.mem_union.mp hh with h | h
    · have h' := step_ref_subset cfg batch s a h
      simpa only [seenCopies_cons,Finset.union_assoc] using
        (Finset.mem_union_left (seenCopies batch as) h')
    · rw [seenCopies_cons]
      exact Finset.mem_union_right _ (Finset.mem_union_right _ h)

theorem run_ref_subset (cfg : Config) (batch : E → List (Edge V)) (as : List E) :
    (run cfg batch as).ref ⊆ seenCopies batch as := by
  simpa [run,initialState] using runFrom_ref_subset cfg batch initialState as

theorem seenCopies_parent (model : BatchModel E V) (as : List E) {e : Edge V}
    (he : e ∈ seenCopies model.copies as) : model.parent e ∈ as := by
  obtain ⟨a,ha,he⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp he)
  simpa [model.parent_mem a e he] using ha

theorem run_ref_parent_seen (cfg : Config) (model : BatchModel E V) (as : List E)
    {e : Edge V} (he : e ∈ (run cfg model.copies as).ref) : model.parent e ∈ as :=
  seenCopies_parent model as (run_ref_subset cfg model.copies as he)

theorem unseen_parent_new (cfg : Config) (model : BatchModel E V) (as : List E)
    {a : E} (ha : a ∉ as) {e : Edge V} (he : e ∈ model.copies a) :
    e ∉ (run cfg model.copies as).ref := by
  intro h
  have hp := run_ref_parent_seen cfg model as h
  rw [model.parent_mem a e he] at hp
  exact ha hp

theorem savedParents_card [DecidableEq E] (parent : Edge V → E) (s : State V) :
    (savedParents parent s).card ≤ s.saved.card := Finset.card_image_le

theorem run_savedParents_cap [DecidableEq E] (cfg : Config) (model : BatchModel E V)
    (as : List E) : (savedParents model.parent (run cfg model.copies as)).card ≤ cfg.uCap :=
  (savedParents_card model.parent _).trans (run_saved_cap cfg model.copies as)

end RobustMatching.R8Acquisition
#print axioms RobustMatching.R8Acquisition.run_ref_parent_seen
#print axioms RobustMatching.R8Acquisition.unseen_parent_new
