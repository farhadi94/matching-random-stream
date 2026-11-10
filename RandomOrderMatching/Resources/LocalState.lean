import RandomOrderMatching.Resources.PhaseBank
import RandomOrderMatching.Acquisition.RetainedRecords

noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Resources
open RandomOrderMatching.Graph RandomOrderMatching.Streaming
open RandomOrderMatching.Phases.Execution
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

def parentStore (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C)
    (a : RandomOrderMatching.Acquisition.State C) : Graph V :=
  a.ref.image model.parent ∪ a.saved.image (fun z => model.parent z.1)

def LocalInvariant (cfg : RandomOrderMatching.Acquisition.Config)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (w : Edge V → ℕ)
    (l : List (Edge V)) : LocalState (RandomOrderMatching.Acquisition.State C) V → Prop
  | .aborted => True
  | .acquiring a => a = RandomOrderMatching.Acquisition.run cfg model.copies l
  | .running a view sf =>
    a = RandomOrderMatching.Acquisition.run cfg model.copies l ∧ a.aborted = false ∧
    a.freezeAt ≠ none ∧ view = acquisitionFrozenView cfg model a ∧
    sf.bank.shared ⊆ parentStore model a ∧
    ∃ tail, tail.Sublist l ∧ sf = suffixRun w view.reference view.eligible tail

theorem frozen_view_step (cfg : RandomOrderMatching.Acquisition.Config)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (a : RandomOrderMatching.Acquisition.State C)
    (e : Edge V) (hf : a.freezeAt ≠ none)
    (ha : (RandomOrderMatching.Acquisition.step cfg model.copies a e).aborted = false) :
    acquisitionFrozenView cfg model (RandomOrderMatching.Acquisition.step cfg model.copies a e) =
      acquisitionFrozenView cfg model a := by
  rw [RandomOrderMatching.Acquisition.frozen_step_surviving cfg model.copies a e hf ha]
  rfl

theorem parentStore_step (cfg : RandomOrderMatching.Acquisition.Config)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (a : RandomOrderMatching.Acquisition.State C)
    (e : Edge V) (hf : a.freezeAt ≠ none)
    (ha : (RandomOrderMatching.Acquisition.step cfg model.copies a e).aborted = false) :
    parentStore model a ⊆ parentStore model (RandomOrderMatching.Acquisition.step cfg model.copies a e) := by
  rw [RandomOrderMatching.Acquisition.frozen_step_surviving cfg model.copies a e hf ha]
  unfold parentStore
  apply Finset.union_subset_union_right
  exact Finset.image_subset_image Finset.subset_union_left

theorem eligible_in_parentStore_step (cfg : RandomOrderMatching.Acquisition.Config)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (a : RandomOrderMatching.Acquisition.State C)
    (e : Edge V) (hf : a.freezeAt ≠ none)
    (ha : (RandomOrderMatching.Acquisition.step cfg model.copies a e).aborted = false)
    (he : (acquisitionFrozenView cfg model a).eligible e) :
    e ∈ parentStore model (RandomOrderMatching.Acquisition.step cfg model.copies a e) := by
  obtain ⟨f,hfcopy,hd⟩ := he
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨(f,a.time+1),
    RandomOrderMatching.Acquisition.frozen_step_retains_copy cfg model.copies a e hf ha hfcopy hd,
    model.parent_mem e f hfcopy⟩

theorem local_invariant_step (cfg : RandomOrderMatching.Acquisition.Config)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (w : Edge V → ℕ)
    (l : List (Edge V)) (s : LocalState (RandomOrderMatching.Acquisition.State C) V)
    (hs : LocalInvariant cfg model w l s) (e : Edge V) :
    LocalInvariant cfg model w (l++[e]) (acquiredLocalStep w cfg model s e) := by
  have hr : RandomOrderMatching.Acquisition.run cfg model.copies (l++[e]) =
      RandomOrderMatching.Acquisition.step cfg model.copies (RandomOrderMatching.Acquisition.run cfg model.copies l) e := by
    simp [RandomOrderMatching.Acquisition.run,RandomOrderMatching.Acquisition.runFrom,List.foldl_append]
  cases s with
  | aborted => trivial
  | acquiring a =>
    change a = RandomOrderMatching.Acquisition.run cfg model.copies l at hs
    subst a
    simp only [acquiredLocalStep,localStep]
    split_ifs with ha
    · trivial
    · have ha' : (RandomOrderMatching.Acquisition.step cfg model.copies
          (RandomOrderMatching.Acquisition.run cfg model.copies l) e).aborted = false := by
        simpa using ha
      cases hf : (RandomOrderMatching.Acquisition.step cfg model.copies
          (RandomOrderMatching.Acquisition.run cfg model.copies l) e).freezeAt with
      | none => simp [acquisitionReadView,hf,LocalInvariant,hr]
      | some tau =>
        simp only [acquisitionReadView,hf]
        refine ⟨hr.symm,ha',by simp [hf],rfl,?_,?_,?_⟩
        · exact Finset.subset_union_left
        · exact []
        · exact ⟨List.nil_sublist _,rfl⟩
  | running a view sf =>
    obtain ⟨ha,hsa,hf,hview,hstore,tail,htail,hsf⟩ := hs
    simp only [acquiredLocalStep,localStep]
    split_ifs with hab
    · trivial
    · have hab' : (RandomOrderMatching.Acquisition.step cfg model.copies a e).aborted = false := by
        simpa using hab
      have hstep := RandomOrderMatching.Acquisition.frozen_step_surviving cfg model.copies a e hf hab'
      have hv := frozen_view_step cfg model a e hf hab'
      refine ⟨by rw [hr,←ha],hab',?_,hview.trans hv.symm,?_,tail++[e],?_,?_⟩
      · simpa only [hstep] using hf
      · change (if view.eligible e then insert e sf.bank.shared else sf.bank.shared) ⊆ _
        have hmono := hstore.trans (parentStore_step cfg model a e hf hab')
        split_ifs with he
        · apply Finset.insert_subset
          · exact eligible_in_parentStore_step cfg model a e hf hab' (hview ▸ he)
          · exact hmono
        · exact hmono
      · exact htail.append (List.Sublist.refl _)
      · rw [hsf]
        simp [suffixRun,List.foldl_append]

theorem local_run_invariant (cfg : RandomOrderMatching.Acquisition.Config)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (w : Edge V → ℕ)
    (l : List (Edge V)) :
    LocalInvariant cfg model w l
      (l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using
      local_invariant_step cfg model w l _ ih e

def localRecords : LocalState (RandomOrderMatching.Acquisition.State C) V → ℕ
  | .aborted => 0
  | .acquiring a => a.ref.card + a.saved.card
  | .running a view sf => a.ref.card + a.saved.card + view.reference.card + suffixRecords sf

def localRecordBound (N n beta uCap W m : ℕ) : ℕ :=
  3 * (N * beta) + 2 * uCap +
    cutoffCountBound m * (N * beta + uCap + W * (n / 2)) + 10000000

theorem parentStore_card (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C)
    (a : RandomOrderMatching.Acquisition.State C) :
    (parentStore model a).card ≤ a.ref.card + a.saved.card :=
  (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

theorem local_records_cap (cfg : RandomOrderMatching.Acquisition.Config)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (w : Edge V → ℕ)
    (l : List (Edge V)) (W m : ℕ) (hw : ∀ e ∈ l, w e ≤ W) (hm : l.length ≤ m) :
    localRecords (l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit) ≤
      localRecordBound (Fintype.card C) (Fintype.card V) cfg.beta cfg.uCap W m := by
  have hi := local_run_invariant cfg model w l
  have hH := RandomOrderMatching.Acquisition.run_reference_cap cfg model.copies l
  have hU := RandomOrderMatching.Acquisition.run_saved_cap cfg model.copies l
  cases hs : l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit with
  | aborted => simp [localRecords]
  | acquiring a =>
    rw [hs] at hi
    change a = RandomOrderMatching.Acquisition.run cfg model.copies l at hi
    simp only [localRecords,hi,localRecordBound]
    omega
  | running a view sf =>
    rw [hs] at hi
    obtain ⟨ha,hsa,hf,hview,hstore,tail,htail,hsf⟩ := hi
    have hH' : a.ref.card ≤ Fintype.card C * cfg.beta := by rw [ha]; omega
    have hU' : a.saved.card ≤ cfg.uCap := by simpa [ha] using hU
    have hv : view.reference.card ≤ Fintype.card C * cfg.beta := by
      rw [hview]
      exact (Finset.card_image_le).trans hH'
    have hB : (sharedBase view.reference view.eligible tail).card ≤
        Fintype.card C * cfg.beta + cfg.uCap := by
      rw [hsf,(suffixRun_fields w view.reference view.eligible tail).1,
        bankRun_shared] at hstore
      exact (Finset.card_le_card hstore).trans
        ((parentStore_card model a).trans (Nat.add_le_add hH' hU'))
    have hw' : ∀e∈view.reference ∪ tail.toFinset,w e≤W := by
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · have hh : view.reference ⊆ l.toFinset := by
          rw [hview,ha]
          exact acquisitionView_reference_subset cfg model _ l
            (RandomOrderMatching.Acquisition.run_ref_subset cfg model.copies l)
        exact hw e (List.mem_toFinset.mp (hh he))
      · exact hw e (htail.subset (List.mem_toFinset.mp he))
    have hc := suffix_records_cap w view.reference view.eligible tail W
      (Fintype.card C * cfg.beta + cfg.uCap) m hw' hB (htail.length_le.trans hm)
    rw [localRecords,hsf]
    unfold localRecordBound
    omega

end RandomOrderMatching.Resources
