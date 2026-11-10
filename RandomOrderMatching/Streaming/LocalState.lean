import RandomOrderMatching.Streaming.SuffixState
noncomputable section
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph
variable {V A : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

/-- The concrete acquisition supplies this view once, at the end of its
first insertion-free epoch. The eligibility predicate is frozen thereafter. -/
structure FrozenView (V : Type*) [DecidableEq V] where
  reference : Graph V
  eligible : Edge V→Prop

inductive LocalState (A V : Type*) [DecidableEq V]
  | acquiring (acquisition : A)
  | running (acquisition : A) (view : FrozenView V) (suffix : SuffixState V)
  | aborted

/-- The edge that triggers freeze belongs to acquisition. Only subsequent
original edges enter the suffix counter, exact suffix buffer, and phase bank.
Abort releases the whole local state and is absorbing. -/
def localStep (w : Edge V→ℕ) (advance : A→Edge V→A) (abort : A→Bool)
    (frozen : A→Option (FrozenView V)) (s : LocalState A V) (e : Edge V) : LocalState A V :=
  match s with
  | .aborted => .aborted
  | .acquiring a =>
    let a' := advance a e
    if abort a' then .aborted else
      match frozen a' with
      | none => .acquiring a'
      | some view => .running a' view (suffixInit view.reference)
  | .running a view suffix =>
    let a' := advance a e
    if abort a' then .aborted else
      .running a' view (suffixStep w view.eligible suffix e)

def localRun (w : Edge V→ℕ) (advance : A→Edge V→A) (abort : A→Bool)
    (frozen : A→Option (FrozenView V)) (initial : LocalState A V) (l : List (Edge V)) :=
  l.foldl (localStep w advance abort frozen) initial

def localAnswer (w : Edge V→ℕ) : LocalState A V→Option (Graph V)
  | .running _ view s => some (suffixOutput w view.reference s)
  | _ => none

theorem localRun_append (w : Edge V→ℕ) (advance : A→Edge V→A) (abort : A→Bool)
    (frozen : A→Option (FrozenView V)) (initial : LocalState A V)
    (l r : List (Edge V)) :
    localRun w advance abort frozen initial (l++r)=
      localRun w advance abort frozen (localRun w advance abort frozen initial l) r := by
  simp [localRun,List.foldl_append]

theorem localRun_aborted (w : Edge V→ℕ) (advance : A→Edge V→A) (abort : A→Bool)
    (frozen : A→Option (FrozenView V)) (l : List (Edge V)) :
    localRun w advance abort frozen .aborted l=.aborted := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    rw [localRun_append,ih]
    rfl

/-- Every surviving post-freeze execution is exactly the suffix implementation,
not a fresh invocation at EOF. The premise is the acquisition's actual cap flag
on each prefix; it is discharged by the acquisition cap-success event. -/
theorem localRun_surviving_suffix (w : Edge V→ℕ) (advance : A→Edge V→A) (abort : A→Bool)
    (frozen : A→Option (FrozenView V)) (a : A) (view : FrozenView V)
    (l : List (Edge V))
    (hsafe : ∀i≤l.length,abort ((l.take i).foldl advance a)=false) :
    localRun w advance abort frozen (.running a view (suffixInit view.reference)) l=
      .running (l.foldl advance a) view (suffixRun w view.reference view.eligible l) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    have hpre : ∀i≤l.length,abort ((l.take i).foldl advance a)=false := by
      intro i hi
      have hh := hsafe i (by simp; omega)
      simpa only [List.take_append_of_le_length hi] using hh
    have hlast : abort (advance (l.foldl advance a) e)=false := by
      have hh := hsafe (l++[e]).length le_rfl
      simpa only [List.take_length,List.foldl_append,List.foldl_cons,List.foldl_nil] using hh
    rw [localRun_append,ih hpre]
    simp only [localRun,List.foldl_cons,List.foldl_nil,localStep,hlast,Bool.false_eq_true,
      ↓reduceIte,List.foldl_append,suffixRun]

/-- Exact causal linkage at the concrete freeze prefix. -/
theorem localRun_after_freeze (w : Edge V→ℕ) (advance : A→Edge V→A) (abort : A→Bool)
    (frozen : A→Option (FrozenView V)) (initial : LocalState A V)
    (pre suffix : List (Edge V)) (a : A) (view : FrozenView V)
    (hfreeze : localRun w advance abort frozen initial pre=
      .running a view (suffixInit view.reference))
    (hsafe : ∀ i ≤ suffix.length,abort ((suffix.take i).foldl advance a)=false) :
    localRun w advance abort frozen initial (pre++suffix)=
      .running (suffix.foldl advance a) view (suffixRun w view.reference view.eligible suffix) := by
  rw [localRun_append,hfreeze]
  exact localRun_surviving_suffix w advance abort frozen a view suffix hsafe

end RandomOrderMatching.Streaming
