import RobustMatching.R8WeightWindowsProbability
import RobustMatching.R8WeightWindowsDecoder

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RobustMatching.R8WeightWindows
open RobustMatching.R2Cut RobustMatching.R7ReductionRetirement
open RobustMatching.R7ReductionActive RobustMatching.R7ReductionGreedy
variable {V : Type*} [DecidableEq V]

def maximum (w : Edge V → ℚ) : List (Edge V) → ℝ
  | [] => 0
  | e::l => max (w e:ℝ) (maximum w l)

theorem maximum_nonneg (w : Edge V → ℚ) (l : List (Edge V)) : 0 ≤ maximum w l := by
  induction l with
  | nil => rfl
  | cons e l ih => exact ih.trans (le_max_right _ _)

theorem le_maximum (w : Edge V → ℚ) (l : List (Edge V)) {e : Edge V}
    (he : e ∈ l) : (w e:ℝ) ≤ maximum w l := by
  induction l with
  | nil => simp at he
  | cons x l ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact le_max_left _ _
    · exact (ih he).trans (le_max_right _ _)

theorem maximum_le (w : Edge V → ℚ) (l : List (Edge V)) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ e ∈ l,(w e:ℝ) ≤ c) : maximum w l ≤ c := by
  induction l with
  | nil => exact hc
  | cons e l ih => exact max_le (h e (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem maximum_append (w : Edge V → ℚ) (l r : List (Edge V)) :
    maximum w (l++r) = max (maximum w l) (maximum w r) := by
  induction l with
  | nil => simp [maximum, max_eq_right (maximum_nonneg w r)]
  | cons e l ih => simp [maximum, ih, max_assoc]

theorem maximum_stream (w : Edge V → ℚ) (stream : ℕ → Edge V) (n : ℕ) :
    maximum w (streamList stream n) = prefixMax (fun e => (w e:ℝ)) stream n := by
  induction n with
  | zero => simp [streamList, maximum, prefixMax]
  | succ n ih =>
    rw [streamList_succ, maximum_append, ih]
    simp only [maximum, prefixMax]
    rw [← max_assoc]
    exact max_eq_left ((prefixMax_nonneg (fun e => (w e:ℝ)) stream n).trans (le_max_left _ _))

namespace Parameters
variable (p : Parameters) (a : Machine V) (w : Edge V → ℚ)

def finalThreshold (nVertices : ℕ) (l : List (Edge V)) : ℝ :=
  ((p.eta:ℝ)/nVertices)*maximum w l
def liveWindows (nVertices : ℕ) (l : List (Edge V)) : Finset ℤ :=
  (p.allWindows w l).filter (fun t => p.finalThreshold w nVertices l < (p.B:ℝ)^(t+(p.k:ℤ)))
def completeOutput (l : List (Edge V)) (t : ℤ) : Graph V :=
  a.answer (p.integerWeight w t) (p.localList w t l)

def winningResidue (T : Finset ℤ) (out : ℤ → Graph V) : Fin (p.k+1) :=
  Classical.choose (Finset.exists_max_image (Finset.univ : Finset (Fin (p.k+1)))
    (fun s => ∑ e ∈ p.residueAnswer T out s,(w e:ℝ)) (by simp))
def decode (T : Finset ℤ) (out : ℤ → Graph V) : Graph V :=
  p.residueAnswer T out (p.winningResidue w T out)
def answer (nVertices : ℕ) (l : List (Edge V)) : Graph V :=
  p.decode w (p.liveWindows w nVertices l) (p.completeOutput a w l)
def actualAnswer (nVertices : ℕ) (stream : ℕ → Edge V) (n : ℕ) : Graph V :=
  p.decode w (p.dictionary w nVertices stream n)
    (fun t => a.output (p.integerWeight w t) (p.retained a w nVertices stream n t))

theorem decode_dominates (T : Finset ℤ) (out : ℤ → Graph V) (s : Fin (p.k+1)) :
    (∑ e ∈ p.residueAnswer T out s,(w e:ℝ)) ≤ ∑ e ∈ p.decode w T out,(w e:ℝ) := by
  exact (Classical.choose_spec (Finset.exists_max_image (Finset.univ : Finset (Fin (p.k+1)))
    (fun s => ∑ e ∈ p.residueAnswer T out s,(w e:ℝ)) (by simp))).2 s (by simp)

theorem completeOutput_valid (hv : a.Valid) (l : List (Edge V)) (t : ℤ) :
    Matching (p.completeOutput a w l t) ∧
    p.completeOutput a w l t ⊆ l.toFinset ∧
    ∀ e ∈ p.completeOutput a w l t,p.contains t (w e) := by
  have hh := hv (p.integerWeight w t) (p.localList w t l)
  refine ⟨hh.1,?_,?_⟩
  · intro e he
    exact List.mem_toFinset.mpr ((List.mem_filter.mp (List.mem_toFinset.mp (hh.2 he))).1)
  · intro e he
    have hm := (List.mem_filter.mp (List.mem_toFinset.mp (hh.2 he))).2
    simpa [belongs] using hm

theorem decode_valid (T : Finset ℤ) (out : ℤ → Graph V) (E : Graph V)
    (hv : ∀ t ∈ T,Matching (out t) ∧ out t ⊆ E) :
    Matching (p.decode w T out) ∧ p.decode w T out ⊆ E := by
  have hlev : ∀ s i,Matching (p.levels T out s i) ∧ p.levels T out s i ⊆ E := by
    intro s i
    unfold levels
    split_ifs with ht
    · exact hv _ ht
    · simp [Matching]
  refine ⟨combine_matching _ (fun i => (hlev _ i).1) _,?_⟩
  intro e he
  obtain ⟨i,hi,hei⟩ := combine_origin _ he
  exact (hlev _ i).2 hei

theorem answer_valid (hv : a.Valid) (nVertices : ℕ) (l : List (Edge V)) :
    Matching (p.answer a w nVertices l) ∧ p.answer a w nVertices l ⊆ l.toFinset := by
  apply p.decode_valid w
  intro t ht
  have hh := p.completeOutput_valid a w hv l t
  exact ⟨hh.1,hh.2.1⟩

theorem allWindows_stream (stream : ℕ → Edge V) (n : ℕ) :
    p.allWindows w (streamList stream n) = seenWindows (fun e => p.windows (w e)) stream n := by
  induction n with
  | zero => simp [allWindows, streamList, seenWindows]
  | succ n ih =>
    change _ = seenWindows (fun e => p.windows (w e)) stream n ∪ p.windows (w (stream n))
    rw [← ih]
    simp [allWindows, streamList_succ, Finset.union_comm]

theorem liveWindows_stream (nVertices : ℕ) (stream : ℕ → Edge V) (n : ℕ) :
    p.liveWindows w nVertices (streamList stream n) = p.dictionary w nVertices stream n := by
  rw [liveWindows, allWindows_stream, dictionary]
  unfold threshold
  rw [
    active_eq_surviving_seen _ _ _ _ (threshold_mono _ _
      (div_nonneg p.eta_real_pos.le (Nat.cast_nonneg _)))]
  simp only [finalThreshold, maximum_stream]

/-- Equality of the actual retired-state EOF decoder and its hypothetical
complete-run analysis, for each input and each fixed local seed tape. -/
theorem actualAnswer_eq (nVertices : ℕ) (stream : ℕ → Edge V) (n : ℕ) :
    p.actualAnswer a w nVertices stream n = p.answer a w nVertices (streamList stream n) := by
  have hout : ∀ t ∈ p.dictionary w nVertices stream n,
      a.output (p.integerWeight w t) (p.retained a w nVertices stream n t) =
        p.completeOutput a w (streamList stream n) t := by
    intro t ht
    rw [p.dictionary_state_eq_filtered a w nVertices stream n t ht]
    rfl
  have hlev : p.levels (p.dictionary w nVertices stream n)
      (fun t => a.output (p.integerWeight w t) (p.retained a w nVertices stream n t)) =
      p.levels (p.dictionary w nVertices stream n) (p.completeOutput a w (streamList stream n)) := by
    funext s i
    unfold levels
    split_ifs with ht
    · exact hout _ ht
    · rfl
  unfold actualAnswer answer
  rw [liveWindows_stream]
  unfold decode winningResidue residueAnswer
  simp only [hlev]

end Parameters
end RobustMatching.R8WeightWindows
