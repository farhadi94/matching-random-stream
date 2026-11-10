import RobustMatching.R8WeightWindowsState

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RobustMatching.R8WeightWindows
open RobustMatching.R2Cut RobustMatching.R7ProbabilityRestriction
variable {V : Type*} [DecidableEq V]

namespace Machine
def Valid (a : Machine V) : Prop := ∀ w l,
  Matching (a.answer w l) ∧ a.answer w l ⊆ l.toFinset

def Good (a : Machine V) (alpha : ℝ) (w : Edge V → ℕ) (l : List (Edge V)) : Prop :=
  ∀ M : Graph V, M ⊆ l.toFinset → Matching M →
    alpha * (∑ e ∈ M, (w e : ℝ)) ≤ ∑ e ∈ a.answer w l, (w e : ℝ)

/-- Complete local random-order approximation contract. It is quantified over
all bounded-integer inputs, not over an adaptively chosen surviving window. -/
structure Contract (a : Machine V) (W : ℕ) (alpha delta : ℝ) : Prop where
  valid : a.Valid
  local_success : ∀ (w : Edge V → ℕ) (l : List (Edge V)), l.Nodup →
    (∀ e ∈ l, 1 ≤ w e ∧ w e ≤ W) →
    permMean l (fun u => if a.Good alpha w u then 0 else 1) ≤ delta
end Machine

theorem permMean_mono {E : Type*} [DecidableEq E] (l : List E)
    (f g : List E → ℝ) (h : ∀ u ∈ l.permutations', f u ≤ g u) :
    permMean l f ≤ permMean l g := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact List.sum_le_sum h

theorem permMean_add {E : Type*} [DecidableEq E] (l : List E)
    (f g : List E → ℝ) :
    permMean l (fun u => f u+g u) = permMean l f+permMean l g := by
  unfold permMean
  rw [List.sum_map_add, add_div]

theorem permMean_sum {E I : Type*} [DecidableEq E] (l : List E)
    (T : Finset I) (f : I → List E → ℝ) :
    permMean l (fun u => ∑ i ∈ T,f i u) = ∑ i ∈ T,permMean l (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [permMean]
  | @insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    rw [permMean_add, ih]

namespace Parameters
variable (p : Parameters) (a : Machine V) (w : Edge V → ℚ)

def allWindows (l : List (Edge V)) : Finset ℤ :=
  l.toFinset.biUnion (fun e => p.windows (w e))

theorem allWindows_count (l : List (Edge V)) (hw : ∀ e, 0 < w e) :
    (p.allWindows w l).card ≤ p.k*l.toFinset.card := by
  apply RobustMatching.R7ReductionFailure.usedWindows_count
  intro e he
  exact (p.windows_card (w e) (hw e)).le

def localGood (alpha : ℝ) (t : ℤ) (l : List (Edge V)) : Prop :=
  a.Good alpha (p.integerWeight w t) (p.localList w t l)

theorem fixed_window_failure (alpha delta : ℝ)
    (hc : a.Contract p.integerRange alpha delta) (l : List (Edge V)) (hl : l.Nodup)
    (t : ℤ) :
    permMean l (fun u => if p.localGood a w alpha t u then 0 else 1) ≤ delta := by
  unfold localGood localList
  rw [permMean_filter l hl (p.belongs w t)
    (fun u => if a.Good alpha (p.integerWeight w t) u then (0:ℝ) else 1)]
  apply hc.local_success
  · exact hl.filter _
  · intro e he
    have hm := (List.mem_filter.mp he).2
    have hh : p.contains t (w e) := by simpa [belongs] using hm
    exact p.normalized_range hh

/-- Union over the fixed graph-nonempty family. No independence between local
executions and no conditioning on the final dictionary is used. -/
theorem all_windows_failure (alpha delta : ℝ)
    (hc : a.Contract p.integerRange alpha delta) (l : List (Edge V)) (hl : l.Nodup) :
    permMean l (fun u => if (∀ t ∈ p.allWindows w l, p.localGood a w alpha t u)
      then 0 else 1) ≤ (p.allWindows w l).card*delta := by
  classical
  let T := p.allWindows w l
  calc
    _ ≤ permMean l (fun u => ∑ t ∈ T,if p.localGood a w alpha t u then 0 else 1) := by
      apply permMean_mono
      intro u hu
      by_cases hh : ∀ t ∈ T, p.localGood a w alpha t u
      · simp only [T] at hh ⊢
        rw [if_pos hh]
        exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
      · push Not at hh
        obtain ⟨t,ht,hbad⟩ := hh
        have hall : ¬∀ t ∈ p.allWindows w l,p.localGood a w alpha t u := by
          intro h
          exact hbad (h t ht)
        rw [if_neg hall]
        have hs := Finset.single_le_sum (f := fun t => if p.localGood a w alpha t u then (0:ℝ) else 1)
          (fun _ _ => by split_ifs <;> norm_num) ht
        simpa [hbad] using hs
    _ = ∑ t ∈ T,permMean l (fun u => if p.localGood a w alpha t u then 0 else 1) :=
      permMean_sum l T _
    _ ≤ ∑ _t ∈ T,delta := Finset.sum_le_sum (fun t _ =>
      p.fixed_window_failure a w alpha delta hc l hl t)
    _ = _ := by simp [T]

end Parameters
end RobustMatching.R8WeightWindows
