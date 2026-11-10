import RobustMatching.R7WeightedPhaseAssemblyBank
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

/-- A global valid greedy fallback is maintained even if every local copy aborts. -/
def fallbackStep (M : Graph V) (e : Edge V) : Graph V :=
  if Matching (insert e M) then insert e M else M

def fallbackRun (l : List (Edge V)) : Graph V := l.foldl fallbackStep ∅

theorem fallbackStep_matching {M : Graph V} (hM : Matching M) (e : Edge V) :
    Matching (fallbackStep M e) := by
  unfold fallbackStep
  split_ifs with h
  · exact h
  · exact hM

theorem fallbackStep_subset (M : Graph V) (e : Edge V) : fallbackStep M e⊆insert e M := by
  unfold fallbackStep
  split_ifs <;> simp

theorem fallbackRun_append (l : List (Edge V)) (e : Edge V) :
    fallbackRun (l++[e])=fallbackStep (fallbackRun l) e := by
  simp [fallbackRun,List.foldl_append]

theorem fallbackRun_matching (l : List (Edge V)) : Matching (fallbackRun l) := by
  induction l using List.reverseRecOn with
  | nil => simp [fallbackRun,Matching]
  | append_singleton l e ih => rw [fallbackRun_append]; exact fallbackStep_matching ih e

theorem fallbackRun_subset (l : List (Edge V)) : fallbackRun l⊆l.toFinset := by
  induction l using List.reverseRecOn with
  | nil => simp [fallbackRun]
  | append_singleton l e ih =>
    rw [fallbackRun_append]
    apply (fallbackStep_subset _ _).trans
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · simp
    · simp only [List.toFinset_append]
      exact Finset.mem_union_left _ (ih hf)

theorem fallbackRun_cap (l : List (Edge V)) : (fallbackRun l).card≤Fintype.card V/2 := by
  have h := Finset.card_le_univ (s:=covered (fallbackRun l))
  rw [covered_card (fallbackRun_matching l)] at h
  omega

end RobustMatching.R8StreamingWrapper
