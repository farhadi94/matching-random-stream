import RandomOrderMatching.Acquisition.Probability.FreshCopies
import RandomOrderMatching.Acquisition.Collector

/-! The actual uncapped timestamped U records are bounded by the number of
underfull ORIGINAL parents. Clearing U on abort is never used as evidence. -/
noncomputable section
open Classical
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

theorem underfullRecords_card_le (lower : ℕ) (H : Graph V) (es : List (Edge V)) (t : ℕ) :
    (underfullRecords lower H es t).card ≤ es.length := by
  exact (Finset.card_image_le).trans
    ((Finset.card_le_card (Finset.filter_subset _ _)).trans (List.toFinset_card_le es))

theorem underfullRecords_empty (lower : ℕ) (H : Graph V) (es : List (Edge V)) (t : ℕ)
    (h : ¬ ∃ e ∈ es,edgeDegree H e<lower) : underfullRecords lower H es t=∅ := by
  have he : es.toFinset.filter (fun e => edgeDegree H e<lower)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e he hd
    exact h ⟨e,List.mem_toFinset.mp he,hd⟩
  simp only [underfullRecords,he,Finset.image_empty]

theorem actual_records_parent_bound (model : BatchModel E V)
    (lower : ℕ) (H : Graph V) (t : ℕ) (as : List E) (hnd : as.Nodup)
    (T : Finset E)
    (hT : ∀ a ∈ as,∀ e ∈ model.copies a,edgeDegree H e<lower → a∈T) :
    (recordsFrom lower H model.copies t as).card ≤ model.kappa*T.card := by
  induction as generalizing t T with
  | nil => simp [recordsFrom]
  | cons a as ih =>
      have hnd' := List.nodup_cons.mp hnd
      by_cases ha : ∃ e ∈ model.copies a,edgeDegree H e<lower
      · have haT : a∈T := by
          obtain ⟨e,he,hd⟩ := ha
          exact hT a (by simp) e he hd
        have hrest : ∀ b∈as,∀ e∈model.copies b,edgeDegree H e<lower → b∈T.erase a := by
          intro b hb e he hd
          apply Finset.mem_erase.mpr
          refine ⟨?_,hT b (by simp [hb]) e he hd⟩
          intro hba
          exact hnd'.1 (hba ▸ hb)
        have hi := ih (t+1) hnd'.2 (T.erase a) hrest
        have hh := (underfullRecords_card_le lower H (model.copies a) (t+1)).trans (model.batch_bound a)
        have hu := Finset.card_union_le (underfullRecords lower H (model.copies a) (t+1))
          (recordsFrom lower H model.copies (t+1) as)
        have hc := Finset.card_erase_add_one haT
        rw [recordsFrom]
        nlinarith
      · rw [recordsFrom,underfullRecords_empty lower H (model.copies a) (t+1) ha,Finset.empty_union]
        exact ih (t+1) hnd'.2 T (fun b hb e he hd => hT b (by simp [hb]) e he hd)

end RandomOrderMatching.Acquisition.Probability
