import RobustMatching.R8StreamingWrapperBracket
import RobustMatching.R7WeightedPhaseAssemblyBank
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R7WeightedPhase RobustMatching.R7WeightedPhaseAssembly
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

structure BankState (V : Type*) [DecidableEq V] where
  count : ℕ
  shared : Graph V
  hosts : ℕ → Graph V

def bankInit (H : Graph V) : BankState V := ⟨0,H,fun _ => ∅⟩

/-- Existing phases process the original label, then a reached cutoff launches
its new phase from the updated shared base. Future cutoffs are not stored. -/
def bankStep (w : Edge V → ℕ) (eligible : Edge V → Prop)
    (s : BankState V) (e : Edge V) : BankState V where
  count := s.count+1
  shared := if eligible e then insert e s.shared else s.shared
  hosts c := if c=s.count+1 ∧ c∈reachedCuts (s.count+1) then
      if eligible e then insert e s.shared else s.shared
    else if c∈reachedCuts s.count then step w ∅ (s.hosts c) e else ∅

def bankRun (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) : BankState V := l.foldl (bankStep w eligible) (bankInit H)

theorem bankRun_append (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) (e : Edge V) :
    bankRun w H eligible (l++[e])=bankStep w eligible (bankRun w H eligible l) e := by
  simp [bankRun,List.foldl_append]

theorem bankRun_count (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) : (bankRun w H eligible l).count=l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih => simp [bankRun_append,bankStep,ih]

theorem sharedBase_append (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) (e : Edge V) :
    sharedBase H eligible (l++[e])=
      if eligible e then insert e (sharedBase H eligible l) else sharedBase H eligible l := by
  classical
  simp only [sharedBase,seenUnderfull,List.take_length]
  ext f
  by_cases he : eligible e <;> simp [he] <;> aesop

theorem bankRun_shared (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) : (bankRun w H eligible l).shared=sharedBase H eligible l := by
  induction l using List.reverseRecOn with
  | nil => simp [bankRun,bankInit,sharedBase,seenUnderfull]
  | append_singleton l e ih => simp only [bankRun_append,bankStep,ih,sharedBase_append]

theorem phaseFinal_append_old (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) (e : Edge V) {c : ℕ} (hc : c≤l.length) :
    phaseFinal w H eligible (l++[e]) c = step w ∅ (phaseFinal w H eligible l c) e := by
  have hi : initial H eligible (l++[e]) c = initial H eligible l c := by
    simp only [initial,seenUnderfull,List.take_append_of_le_length hc]
  simp only [phaseFinal,hi,List.drop_append_of_le_length hc,run,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem phaseFinal_new (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) : phaseFinal w H eligible l l.length=sharedBase H eligible l := by
  simp [phaseFinal,initial,sharedBase,run]

theorem bankRun_host (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) (c : ℕ) :
    (bankRun w H eligible l).hosts c =
      if c∈reachedCuts l.length then phaseFinal w H eligible l c else ∅ := by
  induction l using List.reverseRecOn with
  | nil => simp [bankRun,bankInit,reachedCuts]
  | append_singleton l e ih =>
    rw [bankRun_append]
    simp only [bankStep,bankRun_count,bankRun_shared,List.length_append,List.length_singleton]
    by_cases hc : c∈reachedCuts l.length
    · obtain ⟨j,hj,hle⟩ := mem_reachedCuts.mp hc
      have hnew : c∈reachedCuts (l.length+1) := reachedCuts_mono (by omega) hc
      have hne : c≠l.length+1 := by omega
      simp [hc,hnew,hne,ih,phaseFinal_append_old w H eligible l e hle]
    · by_cases hnew : c∈reachedCuts (l.length+1)
      · obtain ⟨j,hj,hle⟩ := mem_reachedCuts.mp hnew
        have heq : c=l.length+1 := by
          by_contra hn
          have hh : c≤l.length := by omega
          exact hc (mem_reachedCuts.mpr ⟨j,hj,hh⟩)
        subst c
        have hphase := phaseFinal_new w H eligible (l++[e])
        simp only [List.length_append,List.length_singleton] at hphase
        have hnew' : l.length+1∈reachedCuts (l.length+1) := heq ▸ hnew
        simp [heq,hnew',hphase,sharedBase_append]
      · simp [hnew,hc]

def liveBankSupport (s : BankState V) : Graph V :=
  s.shared ∪ (reachedCuts s.count).biUnion s.hosts

theorem activeCuts_reached (l : List (Edge V)) :
    activeCuts (reachedCuts l.length) l=reachedCuts l.length := by
  unfold activeCuts
  exact reachedCuts_filter le_rfl

theorem liveBankSupport_eq (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) :
    liveBankSupport (bankRun w H eligible l)=bankSupport w H eligible l (reachedCuts l.length) := by
  unfold liveBankSupport bankSupport
  rw [bankRun_count,bankRun_shared,activeCuts_reached]
  congr 1
  apply Finset.biUnion_congr rfl
  intro c hc
  simp [bankRun_host,hc]

theorem actual_bank_record_cap (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (l : List (Edge V)) (W : ℕ) (hw : ∀e∈H∪l.toFinset,w e≤W) :
    bankRecordCount w H eligible l (reachedCuts l.length) ≤
      (sharedBase H eligible l).card+cutoffCountBound l.length*(W*(Fintype.card V/2)) := by
  exact (bank_record_cap w H eligible l _ W hw).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (reachedCuts_count l.length)) _)

end RobustMatching.R8StreamingWrapper
