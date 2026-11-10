import RobustMatching.R8StreamingWrapperLocal
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut
variable {V A : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

/-- Before the first acquisition freeze, the local wrapper follows the exact
acquisition fold and has no suffix state. -/
theorem localRun_before_freeze (w : Edge V→ℕ) (advance : A→Edge V→A) (abort : A→Bool)
    (frozen : A→Option (FrozenView V)) (a : A) (l : List (Edge V))
    (hsafe : ∀ i ≤ l.length,abort ((l.take i).foldl advance a)=false)
    (hview : ∀ i ≤ l.length,frozen ((l.take i).foldl advance a)=none) :
    localRun w advance abort frozen (.acquiring a) l=.acquiring (l.foldl advance a) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    have hsp : ∀ i ≤ l.length,abort ((l.take i).foldl advance a)=false := by
      intro i hi
      have hh := hsafe i (by simp; omega)
      simpa only [List.take_append_of_le_length hi] using hh
    have hvp : ∀ i ≤ l.length,frozen ((l.take i).foldl advance a)=none := by
      intro i hi
      have hh := hview i (by simp; omega)
      simpa only [List.take_append_of_le_length hi] using hh
    have hsl : abort (advance (l.foldl advance a) e)=false := by
      simpa only [List.take_length,List.foldl_append,List.foldl_cons,List.foldl_nil]
        using hsafe (l++[e]).length le_rfl
    have hvl : frozen (advance (l.foldl advance a) e)=none := by
      simpa only [List.take_length,List.foldl_append,List.foldl_cons,List.foldl_nil]
        using hview (l++[e]).length le_rfl
    rw [localRun_append,ih hsp hvp]
    simp [localRun,localStep,hsl,hvl,List.foldl_append]

theorem localRun_first_freeze_step (w : Edge V→ℕ) (advance : A→Edge V→A) (abort : A→Bool)
    (frozen : A→Option (FrozenView V)) (initial : LocalState A V)
    (pre : List (Edge V)) (e : Edge V) (a : A) (view : FrozenView V)
    (hpre : localRun w advance abort frozen initial pre=.acquiring a)
    (hsafe : abort (advance a e)=false) (hview : frozen (advance a e)=some view) :
    localRun w advance abort frozen initial (pre++[e])=
      .running (advance a e) view (suffixInit view.reference) := by
  rw [localRun_append,hpre]
  simp [localRun,localStep,hsafe,hview]

/-- First freeze, cap survival and exact post-freeze execution compose without
restarting acquisition, dropping a suffix edge, or adding the freeze edge twice. -/
theorem localRun_first_freeze_then_suffix (w : Edge V→ℕ) (advance : A→Edge V→A)
    (abort : A→Bool) (frozen : A→Option (FrozenView V)) (a : A)
    (pre tail : List (Edge V)) (e : Edge V) (view : FrozenView V)
    (hsafe : ∀ i ≤ pre.length,abort ((pre.take i).foldl advance a)=false)
    (hview : ∀ i ≤ pre.length,frozen ((pre.take i).foldl advance a)=none)
    (hfreezeSafe : abort (advance (pre.foldl advance a) e)=false)
    (hfreezeView : frozen (advance (pre.foldl advance a) e)=some view)
    (htail : ∀ i ≤ tail.length,abort ((tail.take i).foldl advance
      (advance (pre.foldl advance a) e))=false) :
    localRun w advance abort frozen (.acquiring a) ((pre++[e])++tail)=
      .running (tail.foldl advance (advance (pre.foldl advance a) e)) view
        (suffixRun w view.reference view.eligible tail) := by
  apply localRun_after_freeze w advance abort frozen (.acquiring a) (pre++[e]) tail
    (advance (pre.foldl advance a) e) view
  · exact localRun_first_freeze_step w advance abort frozen (.acquiring a) pre e _ view
      (localRun_before_freeze w advance abort frozen a pre hsafe hview) hfreezeSafe hfreezeView
  · exact htail

end RobustMatching.R8StreamingWrapper
