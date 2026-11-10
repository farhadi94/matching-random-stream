import RandomOrderMatching.Weights.Windows.Arithmetic
import RandomOrderMatching.Probability.Restriction

noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Weights.Windows
open RandomOrderMatching.Graph RandomOrderMatching.Weights.Reduction.Retirement
open RandomOrderMatching.Weights.Reduction.LiveDictionary
variable {V : Type*} [DecidableEq V]

/-- The bounded-integer algorithm is the sole algorithmic input to the
range reduction. Its state includes all counters and fixed seed tapes. -/
structure Machine (V : Type*) [DecidableEq V] where
  State : Type*
  initial : (Edge V → ℕ) → State
  step : (Edge V → ℕ) → State → Edge V → State
  output : (Edge V → ℕ) → State → Graph V

namespace Machine
def run (a : Machine V) (w : Edge V → ℕ) (l : List (Edge V)) : a.State :=
  l.foldl (a.step w) (a.initial w)
def answer (a : Machine V) (w : Edge V → ℕ) (l : List (Edge V)) : Graph V :=
  a.output w (a.run w l)
end Machine

def streamList {E : Type*} (stream : ℕ → E) (n : ℕ) : List E :=
  List.ofFn (fun i : Fin n => stream i)

theorem streamList_succ {E : Type*} (stream : ℕ → E) (n : ℕ) :
    streamList stream (n+1) = streamList stream n ++ [stream n] := by
  rw [streamList, List.ofFn_succ']
  simp [streamList, List.concat_eq_append]

namespace Parameters
variable (p : Parameters) (a : Machine V) (w : Edge V → ℚ)

def integerWeight (t : ℤ) : Edge V → ℕ := fun e => p.normalized t (w e)
def belongs (t : ℤ) (e : Edge V) : Bool := by
  classical
  exact decide (p.contains t (w e))
def localList (t : ℤ) (l : List (Edge V)) : List (Edge V) := l.filter (p.belongs w t)
def threshold (nVertices : ℕ) (stream : ℕ → Edge V) (n : ℕ) : ℝ :=
  ((p.eta : ℝ) / nVertices) * prefixMax (fun e => (w e : ℝ)) stream n

def dictionary (nVertices : ℕ) (stream : ℕ → Edge V) (n : ℕ) : Finset ℤ :=
  activeWindows (fun e => p.windows (w e)) stream (p.threshold w nVertices stream)
    (fun t => (p.B : ℝ)^(t+(p.k:ℤ))) n

def retained (nVertices : ℕ) (stream : ℕ → Edge V) (n : ℕ) (t : ℤ) : a.State :=
  retiredState (fun t => a.initial (p.integerWeight w t))
    (fun t => a.step (p.integerWeight w t)) (p.belongs w) stream
    (p.threshold w nVertices stream) (fun t => (p.B : ℝ)^(t+(p.k:ℤ))) n t

theorem full_eq_filtered (stream : ℕ → Edge V) (n : ℕ) (t : ℤ) :
    fullState (fun t => a.initial (p.integerWeight w t))
      (fun t => a.step (p.integerWeight w t)) (p.belongs w) stream n t =
    a.run (p.integerWeight w t) (p.localList w t (streamList stream n)) := by
  induction n with
  | zero => simp [fullState, Machine.run, localList, streamList]
  | succ n ih =>
    rw [streamList_succ]
    simp only [localList, List.filter_append, Machine.run, List.foldl_append]
    change (if p.belongs w t (stream n) then
      a.step (p.integerWeight w t)
        (fullState (fun t => a.initial (p.integerWeight w t))
          (fun t => a.step (p.integerWeight w t)) (p.belongs w) stream n t) (stream n)
      else _) = _
    rw [ih]
    cases h : p.belongs w t (stream n) <;>
      simp [h, Machine.run, localList]
    exact ih

theorem surviving_state_eq_filtered (nVertices : ℕ) (stream : ℕ → Edge V)
    (n : ℕ) (t : ℤ)
    (hlive : p.threshold w nVertices stream n < (p.B : ℝ)^(t+(p.k:ℤ))) :
    p.retained a w nVertices stream n t =
      a.run (p.integerWeight w t) (p.localList w t (streamList stream n)) := by
  unfold retained threshold at *
  rw [running_max_survivor _ _ _ _ _ _
    (div_nonneg p.eta_real_pos.le (Nat.cast_nonneg nVertices)) n t hlive]
  exact p.full_eq_filtered a w stream n t

theorem dictionary_count (nVertices : ℕ) (stream : ℕ → Edge V)
    (hw : ∀ e, 0 < w e) (h : ℕ)
    (hscale : (p.B : ℝ)^(-(h:ℤ)) ≤ (p.eta:ℝ)/nVertices) (n : ℕ) :
    (p.dictionary w nVertices stream n).card ≤ p.k+h+1 := by
  apply actual_live_count (fun e => p.windows (w e)) stream
    (fun e => (w e : ℝ)) (fun e => by exact_mod_cast hw e)
    p.base_real (div_nonneg p.eta_real_pos.le (Nat.cast_nonneg _)) hscale
  intro e t ht
  have hh := ((p.mem_windows (hw e) t).mp ht).1
  exact_mod_cast hh

theorem dictionary_live (nVertices : ℕ) (stream : ℕ → Edge V)
    (n : ℕ) (t : ℤ) (ht : t ∈ p.dictionary w nVertices stream n) :
    p.threshold w nVertices stream n < (p.B : ℝ)^(t+(p.k:ℤ)) := by
  have hm : Monotone (p.threshold w nVertices stream) :=
    threshold_mono _ _ (div_nonneg p.eta_real_pos.le (Nat.cast_nonneg _))
  rw [dictionary, active_eq_surviving_seen _ _ _ _ hm] at ht
  exact (Finset.mem_filter.mp ht).2

theorem dictionary_state_eq_filtered (nVertices : ℕ) (stream : ℕ → Edge V)
    (n : ℕ) (t : ℤ) (ht : t ∈ p.dictionary w nVertices stream n) :
    p.retained a w nVertices stream n t =
      a.run (p.integerWeight w t) (p.localList w t (streamList stream n)) :=
  p.surviving_state_eq_filtered a w nVertices stream n t
    (p.dictionary_live w nVertices stream n t ht)

end Parameters
end RandomOrderMatching.Weights.Windows
