import RandomOrderMatching.Acquisition.Cleanup

/-! Actual insertion decisions and fixed-order copied-edge batch folds. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Acquisition
open RandomOrderMatching.Graph
variable {V : Type*} [Fintype V] [DecidableEq V]

def insertable (lower : ℕ) (H : Graph V) (e : Edge V) : Prop :=
  e ∉ H ∧ edgeDegree H e < lower

def edgeUpdate (beta lower : ℕ) (H : Graph V) (e : Edge V) : Graph V × Bool :=
  if insertable lower H e then (cleanup beta (insert e H),true) else (H,false)

theorem edgeUpdate_false_iff (beta lower : ℕ) (H : Graph V) (e : Edge V) :
    (edgeUpdate beta lower H e).2=false ↔ ¬insertable lower H e := by
  by_cases h : insertable lower H e <;> simp [edgeUpdate,h]

theorem edgeUpdate_noinsert (beta lower : ℕ) (H : Graph V) (e : Edge V)
    (h : (edgeUpdate beta lower H e).2=false) : (edgeUpdate beta lower H e).1=H := by
  simp [edgeUpdate,(edgeUpdate_false_iff beta lower H e).mp h]

theorem edgeUpdate_subset (beta lower : ℕ) (H : Graph V) (e : Edge V) :
    (edgeUpdate beta lower H e).1 ⊆ insert e H := by
  unfold edgeUpdate
  split_ifs
  · exact cleanup_subset beta _
  · exact Finset.subset_insert _ _

theorem edgeUpdate_progress (beta lower : ℕ) (hl : lower+1≤beta)
    (H : Graph V) (e : Edge V) :
    potential beta H+(if (edgeUpdate beta lower H e).2 then 1 else 0) ≤
      potential beta (edgeUpdate beta lower H e).1 := by
  by_cases hi : insertable lower H e
  · have hdeg := hi.2
    have hh : edgeDegree H e+2≤beta := by omega
    have hz : (edgeDegree H e : ℤ)+2≤(beta : ℤ) := by exact_mod_cast hh
    have hp := insert_potential_increase beta e hi.1 (by linarith)
    have hc := cleanup_potential beta (insert e H)
    simp only [edgeUpdate,if_pos hi,Prod.fst,Prod.snd,ite_true]
    linarith
  · simp [edgeUpdate,hi]

theorem edgeUpdate_upper (beta lower : ℕ) (hb : 1≤beta) (hl : lower+1≤beta)
    (H : Graph V) (hH : Upper beta H) (e : Edge V) :
    Upper beta (edgeUpdate beta lower H e).1 := by
  by_cases hi : insertable lower H e
  · simp only [edgeUpdate,if_pos hi,Prod.fst]
    apply cleanup_upper
    have hp0 := potential_nonneg hb hH
    have hdeg := hi.2
    have hh : edgeDegree H e+2≤beta := by omega
    have hz : (edgeDegree H e : ℤ)+2≤(beta : ℤ) := by exact_mod_cast hh
    have hp := insert_potential_increase beta e hi.1 (by linarith)
    linarith
  · simpa [edgeUpdate,hi] using hH

def batchUpdate (beta lower : ℕ) : Graph V → List (Edge V) → Graph V × Bool
  | H,[] => (H,false)
  | H,e::es =>
    let h := edgeUpdate beta lower H e
    let t := batchUpdate beta lower h.1 es
    (t.1,h.2 || t.2)

theorem batchUpdate_upper (beta lower : ℕ) (hb : 1≤beta) (hl : lower+1≤beta)
    (H : Graph V) (hH : Upper beta H) (es : List (Edge V)) :
    Upper beta (batchUpdate beta lower H es).1 := by
  induction es generalizing H with
  | nil => exact hH
  | cons e es ih => exact ih _ (edgeUpdate_upper beta lower hb hl H hH e)

theorem batchUpdate_progress (beta lower : ℕ) (hl : lower+1≤beta)
    (H : Graph V) (es : List (Edge V)) :
    potential beta H+(if (batchUpdate beta lower H es).2 then 1 else 0) ≤
      potential beta (batchUpdate beta lower H es).1 := by
  induction es generalizing H with
  | nil => simp [batchUpdate]
  | cons e es ih =>
    have hh := edgeUpdate_progress beta lower hl H e
    have ht := ih (edgeUpdate beta lower H e).1
    simp only [batchUpdate]
    have hind (a b : Bool) : (if a || b then (1 : ℤ) else 0) ≤
        (if a then 1 else 0)+(if b then 1 else 0) := by
      cases a <;> cases b <;> norm_num
    have hs := hind (edgeUpdate beta lower H e).2
      (batchUpdate beta lower (edgeUpdate beta lower H e).1 es).2
    calc
      _ ≤ potential beta H+((if (edgeUpdate beta lower H e).2 then (1 : ℤ) else 0)+
          (if (batchUpdate beta lower (edgeUpdate beta lower H e).1 es).2 then 1 else 0)) :=
        add_le_add le_rfl hs
      _ = (potential beta H+(if (edgeUpdate beta lower H e).2 then (1 : ℤ) else 0))+
          (if (batchUpdate beta lower (edgeUpdate beta lower H e).1 es).2 then 1 else 0) := by ring
      _ ≤ potential beta (edgeUpdate beta lower H e).1+
          (if (batchUpdate beta lower (edgeUpdate beta lower H e).1 es).2 then 1 else 0) :=
        add_le_add hh le_rfl
      _ ≤ _ := ht

theorem batchUpdate_noinsert (beta lower : ℕ) (H : Graph V) (es : List (Edge V))
    (h : (batchUpdate beta lower H es).2=false) : (batchUpdate beta lower H es).1=H := by
  induction es generalizing H with
  | nil => rfl
  | cons e es ih =>
    have hh : (edgeUpdate beta lower H e).2=false ∧
        (batchUpdate beta lower (edgeUpdate beta lower H e).1 es).2=false := by
      simpa only [batchUpdate,Bool.or_eq_false_iff] using h
    change (batchUpdate beta lower (edgeUpdate beta lower H e).1 es).1=H
    rw [ih _ hh.2,edgeUpdate_noinsert beta lower H e hh.1]

theorem batchUpdate_false_iff (beta lower : ℕ) (H : Graph V) (es : List (Edge V)) :
    (batchUpdate beta lower H es).2=false ↔ ∀ e∈es,¬insertable lower H e := by
  induction es generalizing H with
  | nil => simp [batchUpdate]
  | cons e es ih =>
    constructor
    · intro hh
      have ht : (edgeUpdate beta lower H e).2=false ∧
          (batchUpdate beta lower (edgeUpdate beta lower H e).1 es).2=false := by
        simpa only [batchUpdate,Bool.or_eq_false_iff] using hh
      have hhead := (edgeUpdate_false_iff beta lower H e).mp ht.1
      have htail := (ih _).mp ht.2
      rw [edgeUpdate_noinsert beta lower H e ht.1] at htail
      simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hhead htail
    · intro hh
      have hhead : ¬insertable lower H e := hh e (List.mem_cons_self ..)
      have htail : ∀ f∈es,¬insertable lower H f := fun f hf => hh f (List.mem_cons_of_mem _ hf)
      have he := (edgeUpdate_false_iff beta lower H e).mpr hhead
      simp only [batchUpdate]
      rw [he,edgeUpdate_noinsert beta lower H e he]
      simpa using (ih H).mpr htail

theorem batchUpdate_subset (beta lower : ℕ) (H : Graph V) (es : List (Edge V)) :
    (batchUpdate beta lower H es).1 ⊆ H ∪ es.toFinset := by
  induction es generalizing H with
  | nil => simp [batchUpdate]
  | cons e es ih =>
    intro f hf
    have ht := ih (edgeUpdate beta lower H e).1 hf
    rcases Finset.mem_union.mp ht with hh | hh
    · rcases Finset.mem_insert.mp (edgeUpdate_subset beta lower H e hh) with he | hH
      · subst f; simp
      · exact Finset.mem_union_left _ hH
    · exact Finset.mem_union_right _ (by simpa using Finset.mem_insert_of_mem hh)

end RandomOrderMatching.Acquisition
#print axioms RandomOrderMatching.Acquisition.batchUpdate_false_iff
#print axioms RandomOrderMatching.Acquisition.batchUpdate_progress
