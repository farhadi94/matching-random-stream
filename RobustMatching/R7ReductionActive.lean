import RobustMatching.R7ReductionRetirement

/-! The implemented finite dictionary of live window indices. -/
noncomputable section
namespace RobustMatching.R7ReductionActive
open RobustMatching.R7ReductionRetirement
variable {E I : Type*} [DecidableEq I]

def seenWindows (windows : E → Finset I) (stream : ℕ → E) : ℕ → Finset I :=
  Nat.rec ∅ (fun n previous => previous ∪ windows (stream n))

def activeWindows (windows : E → Finset I) (stream : ℕ → E)
    (threshold : ℕ → ℝ) (upper : I → ℝ) : ℕ → Finset I := by
  classical
  exact Nat.rec ∅ (fun n previous =>
    (previous ∪ windows (stream n)).filter (fun i => threshold (n+1) < upper i))

theorem seen_origin (windows : E → Finset I) (stream : ℕ → E) {n : ℕ} {i : I}
    (hi : i ∈ seenWindows windows stream n) :
    ∃ j < n,i ∈ windows (stream j) := by
  induction n with
  | zero => simp [seenWindows] at hi
  | succ n ih =>
    change i ∈ seenWindows windows stream n ∪ windows (stream n) at hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j,hj,hi⟩ := ih hi
      exact ⟨j,by omega,hi⟩
    · exact ⟨n,Nat.lt_succ_self n,hi⟩

/-- Exact dictionary invariant, including arbitrary large jumps of the maximum. -/
theorem active_eq_surviving_seen (windows : E → Finset I) (stream : ℕ → E)
    (threshold : ℕ → ℝ) (upper : I → ℝ) (hmono : Monotone threshold) (n : ℕ) :
    activeWindows windows stream threshold upper n =
      (seenWindows windows stream n).filter (fun i => threshold n < upper i) := by
  classical
  induction n with
  | zero => simp [activeWindows,seenWindows]
  | succ n ih =>
    change ((activeWindows windows stream threshold upper n) ∪ windows (stream n)).filter _ =
      ((seenWindows windows stream n) ∪ windows (stream n)).filter _
    rw [ih]
    ext i
    simp only [Finset.mem_filter,Finset.mem_union]
    have hprev : threshold (n+1) < upper i → threshold n < upper i :=
      fun h => (hmono (Nat.le_succ n)).trans_lt h
    aesop

/-- Hard record-index bound for the actual finite dictionary of geometric windows. -/
theorem actual_live_count (windows : E → Finset ℤ) (stream : ℕ → E)
    (weight : E → ℝ) (hw : ∀ e,0 < weight e) {B c : ℝ} {k h : ℕ}
    (hB : 1 < B) (hc : 0 ≤ c) (hscale : B^(-(h:ℤ)) ≤ c)
    (hlower : ∀ e,∀ t ∈ windows e,B^t ≤ weight e) (n : ℕ) :
    (activeWindows windows stream (fun n => c*prefixMax weight stream n)
      (fun t => B^(t+(k:ℤ))) n).card ≤ k+h+1 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [activeWindows]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hm : 0 < prefixMax weight stream n :=
    (hw (stream 0)).trans_le (weight_le_prefixMax weight stream hnpos)
  rw [active_eq_surviving_seen windows stream _ _ (threshold_mono weight stream hc)]
  apply live_window_count_base _ hB hm hscale
  intro t ht
  obtain ⟨htseen,htlive⟩ := Finset.mem_filter.mp ht
  obtain ⟨j,hj,htj⟩ := seen_origin windows stream htseen
  exact ⟨(hlower (stream j) t htj).trans (weight_le_prefixMax weight stream hj),htlive⟩

end RobustMatching.R7ReductionActive

#print axioms RobustMatching.R7ReductionActive.active_eq_surviving_seen
#print axioms RobustMatching.R7ReductionActive.actual_live_count
