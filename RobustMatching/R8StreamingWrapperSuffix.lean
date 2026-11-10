import RobustMatching.R8StreamingWrapperBank
import RobustMatching.R8StreamingWrapperBuffers
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R7WeightedPhase RobustMatching.R7WeightedPhaseAssembly
open RobustMatching.R6FableImportance
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0

structure SuffixState (V : Type*) [DecidableEq V] where
  bank : BankState V
  complete : Option (List (Edge V))

def suffixInit (H : Graph V) : SuffixState V := ⟨bankInit H,some []⟩
def suffixStep (w : Edge V→ℕ) (eligible : Edge V→Prop) (s : SuffixState V)
    (e : Edge V) : SuffixState V :=
  ⟨bankStep w eligible s.bank e,bufferStep 10000000 s.complete e⟩
def suffixRun (w : Edge V→ℕ) (H : Graph V) (eligible : Edge V→Prop)
    (l : List (Edge V)) : SuffixState V := l.foldl (suffixStep w eligible) (suffixInit H)

theorem suffixRun_fields (w : Edge V→ℕ) (H : Graph V) (eligible : Edge V→Prop)
    (l : List (Edge V)) :
    (suffixRun w H eligible l).bank=bankRun w H eligible l ∧
    (suffixRun w H eligible l).complete=bufferRun 10000000 l := by
  induction l using List.reverseRecOn with
  | nil => constructor <;> rfl
  | append_singleton l e ih =>
    simp only [suffixRun,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (suffixStep w eligible (suffixRun w H eligible l) e).bank=_ ∧
      (suffixStep w eligible (suffixRun w H eligible l) e).complete=_
    simp only [suffixStep,ih.1,ih.2,bankRun_append,bufferRun_append]
    trivial

def suffixOutput (w : Edge V→ℕ) (H : Graph V) (s : SuffixState V) : Graph V :=
  match s.complete with
  | some b => decode w (H∪b.toFinset)
  | none => decode w (liveBankSupport s.bank)

theorem suffixOutput_spec (w : Edge V→ℕ) (H : Graph V) (eligible : Edge V→Prop)
    (l : List (Edge V)) :
    Matching (suffixOutput w H (suffixRun w H eligible l)) ∧
    suffixOutput w H (suffixRun w H eligible l)⊆H∪l.toFinset := by
  unfold suffixOutput
  rw [(suffixRun_fields w H eligible l).2]
  cases hb : bufferRun 10000000 l with
  | none =>
    simp only [(suffixRun_fields w H eligible l).1,liveBankSupport_eq]
    exact ⟨decode_matching _ _,(decode_subset _ _).trans (bank_subset_input _ _ _ _ _)⟩
  | some b =>
    have he := ((bufferRun_some_iff 10000000 l b).mp hb).2
    subst b
    exact ⟨decode_matching _ _,decode_subset _ _⟩

theorem suffixOutput_short_exact (w : Edge V→ℕ) (H : Graph V) (eligible : Edge V→Prop)
    (l : List (Edge V)) (hl : l.length≤10000000) :
    (∑e∈suffixOutput w H (suffixRun w H eligible l),(w e:ℝ))=
      opt (fun e => (w e:ℝ)) (H∪l.toFinset) := by
  unfold suffixOutput
  rw [(suffixRun_fields w H eligible l).2,bufferRun_exact,if_pos hl]
  exact decode_real_weight _ _

theorem suffixOutput_dominates_bank (w : Edge V→ℕ) (H : Graph V) (eligible : Edge V→Prop)
    (l : List (Edge V)) :
    opt (fun e => (w e:ℝ)) (bankSupport w H eligible l (reachedCuts l.length)) ≤
    ∑e∈suffixOutput w H (suffixRun w H eligible l),(w e:ℝ) := by
  unfold suffixOutput
  rw [(suffixRun_fields w H eligible l).2]
  cases hb : bufferRun 10000000 l with
  | none =>
    rw [(suffixRun_fields w H eligible l).1,liveBankSupport_eq,decode_real_weight]
  | some b =>
    have he := ((bufferRun_some_iff 10000000 l b).mp hb).2
    subst b
    rw [decode_real_weight,opt_eq_natOpt,opt_eq_natOpt]
    exact_mod_cast natOpt_mono w (bank_subset_input w H eligible l (reachedCuts l.length))

theorem suffixOutput_selected_phase (w : Edge V→ℕ) (H : Graph V) (eligible : Edge V→Prop)
    (l : List (Edge V)) (hl : 10000000≤l.length) :
    opt (fun e => (w e:ℝ)) (phaseFinal w H eligible l (selectedCutoff l.length)) ≤
    ∑e∈suffixOutput w H (suffixRun w H eligible l),(w e:ℝ) := by
  have hp : selectedCutoff l.length∈activeCuts (reachedCuts l.length) l := by
    rw [activeCuts_reached]
    exact selected_cutoff_reached hl
  have hh := phase_subset_bank w H eligible l (reachedCuts l.length) _ hp
  have ho : opt (fun e => (w e:ℝ)) (phaseFinal w H eligible l (selectedCutoff l.length)) ≤
      opt (fun e => (w e:ℝ)) (bankSupport w H eligible l (reachedCuts l.length)) := by
    rw [opt_eq_natOpt,opt_eq_natOpt]
    exact_mod_cast natOpt_mono w hh
  exact ho.trans (suffixOutput_dominates_bank w H eligible l)

theorem suffixOutput_dominates_base (w : Edge V→ℕ) (H : Graph V) (eligible : Edge V→Prop)
    (l : List (Edge V)) :
    opt (fun e => (w e:ℝ)) (sharedBase H eligible l) ≤
    ∑e∈suffixOutput w H (suffixRun w H eligible l),(w e:ℝ) := by
  have hb : opt (fun e => (w e:ℝ)) (sharedBase H eligible l) ≤
      opt (fun e => (w e:ℝ)) (bankSupport w H eligible l (reachedCuts l.length)) := by
    rw [opt_eq_natOpt,opt_eq_natOpt]
    exact_mod_cast natOpt_mono w (shared_subset_bank w H eligible l (reachedCuts l.length))
  exact hb.trans (suffixOutput_dominates_bank w H eligible l)

/-- Only a bracketed execution supplies the phase-transfer premise. Analytic
surrogates may satisfy the profile for every clock outcome; output dominance
is applied separately on the bracket event. -/
theorem suffixOutput_dominates_surrogate (w : Edge V→ℕ) (H : Graph V)
    (eligible : Edge V→Prop) (l : List (Edge V)) (hl : 10000000≤l.length)
    (b transfer : ℝ)
    (hb : b≤opt (fun e => (w e:ℝ)) (sharedBase H eligible l))
    (ht : transfer≤opt (fun e => (w e:ℝ)) (phaseFinal w H eligible l (selectedCutoff l.length))) :
    max b transfer≤∑e∈suffixOutput w H (suffixRun w H eligible l),(w e:ℝ) :=
  max_le (hb.trans (suffixOutput_dominates_base w H eligible l))
    (ht.trans (suffixOutput_selected_phase w H eligible l hl))

end RobustMatching.R8StreamingWrapper
