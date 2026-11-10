import RobustMatching.R8StreamingWrapperBuffers
import RobustMatching.R8StreamingWrapperFallback
import RobustMatching.R8StreamingWrapperDyadic
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R7WeightedPhaseAssembly RobustMatching.R7WeightedPhase
open RobustMatching.R6FableImportance
variable {V A : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
attribute [local instance] Classical.propDecidable

abbrev ScaleIndex (n Q : ℕ) := {M : ℕ // M∈scales n Q}

/-- The state has one slot for each predetermined eligible dyadic scale.
The acquisition/suffix engine stored in each slot is supplied separately. -/
structure OuterState (V A : Type*) [DecidableEq V] (n Q : ℕ) where
  count : ℕ
  complete : Option (List (Edge V))
  fallback : Graph V
  copies : ScaleIndex n Q → A

def outerInit (n Q : ℕ) (init : ℕ→A) : OuterState V A n Q :=
  ⟨0,some [],∅,fun M => init M.val⟩

def outerStep (n Q cap : ℕ) (advance : ℕ→A→Edge V→A)
    (s : OuterState V A n Q) (e : Edge V) : OuterState V A n Q :=
  ⟨s.count+1,bufferStep cap s.complete e,fallbackStep s.fallback e,
    fun M => advance M.val (s.copies M) e⟩

def outerRun (n Q cap : ℕ) (init : ℕ→A) (advance : ℕ→A→Edge V→A)
    (l : List (Edge V)) : OuterState V A n Q :=
  l.foldl (outerStep n Q cap advance) (outerInit n Q init)

theorem outerRun_fields (n Q cap : ℕ) (init : ℕ→A) (advance : ℕ→A→Edge V→A)
    (l : List (Edge V)) :
    (outerRun n Q cap init advance l).count=l.length ∧
    (outerRun n Q cap init advance l).complete=bufferRun cap l ∧
    (outerRun n Q cap init advance l).fallback=fallbackRun l ∧
    ∀M,(outerRun n Q cap init advance l).copies M=
      l.foldl (advance M.val) (init M.val) := by
  induction l using List.reverseRecOn with
  | nil => simp [outerRun,outerInit,bufferRun,fallbackRun]
  | append_singleton l e ih =>
    simp only [outerRun,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (outerStep n Q cap advance (outerRun n Q cap init advance l) e).count=_ ∧
      (outerStep n Q cap advance (outerRun n Q cap init advance l) e).complete=_ ∧
      (outerStep n Q cap advance (outerRun n Q cap init advance l) e).fallback=_ ∧ _
    simp only [outerStep,ih.1,ih.2.1,ih.2.2.1,List.length_append,List.length_singleton,
      bufferRun_append,fallbackRun_append]
    refine ⟨trivial,trivial,trivial,?_⟩
    intro M
    change advance M.val ((outerRun n Q cap init advance l).copies M) e = _
    rw [ih.2.2.2 M]

/-- EOF chooses the unique dyadic scale determined by the final count.
No copy is initialized at EOF. An absent/aborted local answer invokes fallback. -/
def selectedAnswer (n Q : ℕ) (answer : ℕ→A→Option (Graph V))
    (s : OuterState V A n Q) : Option (Graph V) :=
  if h : chosenScale s.count∈scales n Q then
    answer (chosenScale s.count) (s.copies ⟨chosenScale s.count,h⟩)
  else none

def outerOutput (n Q : ℕ) (w : Edge V→ℕ) (answer : ℕ→A→Option (Graph V))
    (s : OuterState V A n Q) : Graph V :=
  match s.complete with
  | some b => decode w b.toFinset
  | none => (selectedAnswer n Q answer s).getD s.fallback

theorem selectedAnswer_run (n Q cap : ℕ) (init : ℕ→A) (advance : ℕ→A→Edge V→A)
    (answer : ℕ→A→Option (Graph V)) (l : List (Edge V))
    (hm : chosenScale l.length∈scales n Q) :
    selectedAnswer n Q answer (outerRun n Q cap init advance l)=
      answer (chosenScale l.length) (l.foldl (advance (chosenScale l.length))
        (init (chosenScale l.length))) := by
  unfold selectedAnswer
  simp only [(outerRun_fields n Q cap init advance l).1]
  rw [dif_pos hm,(outerRun_fields n Q cap init advance l).2.2.2]

theorem outerOutput_full_exact (n Q cap : ℕ) (init : ℕ→A) (advance : ℕ→A→Edge V→A)
    (answer : ℕ→A→Option (Graph V)) (w : Edge V→ℕ) (l : List (Edge V))
    (hl : l.length≤cap) :
    outerOutput n Q w answer (outerRun n Q cap init advance l)=decode w l.toFinset := by
  unfold outerOutput
  rw [(outerRun_fields n Q cap init advance l).2.1,bufferRun_exact,if_pos hl]

theorem outerOutput_overflow_selected (n Q cap : ℕ) (init : ℕ→A)
    (advance : ℕ→A→Edge V→A) (answer : ℕ→A→Option (Graph V))
    (w : Edge V→ℕ) (l : List (Edge V)) (hl : cap<l.length)
    (hm : chosenScale l.length∈scales n Q) :
    outerOutput n Q w answer (outerRun n Q cap init advance l)=
      (answer (chosenScale l.length) (l.foldl (advance (chosenScale l.length))
        (init (chosenScale l.length)))).getD (fallbackRun l) := by
  unfold outerOutput
  rw [(outerRun_fields n Q cap init advance l).2.1,bufferRun_exact,if_neg (by omega)]
  rw [selectedAnswer_run n Q cap init advance answer l hm,
    (outerRun_fields n Q cap init advance l).2.2.1]

/-- Generic fan-out/EOF composition. Engine validity is explicitly a separate
input; no acquisition or approximation theorem is assumed silently. -/
theorem outerOutput_valid (n Q cap : ℕ) (init : ℕ→A) (advance : ℕ→A→Edge V→A)
    (answer : ℕ→A→Option (Graph V)) (w : Edge V→ℕ) (l : List (Edge V))
    (hengine : ∀M∈scales n Q,∀P,answer M (l.foldl (advance M) (init M))=some P →
      Matching P ∧ P⊆l.toFinset) :
    Matching (outerOutput n Q w answer (outerRun n Q cap init advance l)) ∧
    outerOutput n Q w answer (outerRun n Q cap init advance l)⊆l.toFinset := by
  by_cases hl : l.length≤cap
  · rw [outerOutput_full_exact n Q cap init advance answer w l hl]
    exact ⟨decode_matching _ _,decode_subset _ _⟩
  · unfold outerOutput
    rw [(outerRun_fields n Q cap init advance l).2.1,bufferRun_exact,if_neg hl]
    by_cases hm : chosenScale l.length∈scales n Q
    · rw [selectedAnswer_run n Q cap init advance answer l hm]
      cases ha : answer (chosenScale l.length)
        (l.foldl (advance (chosenScale l.length)) (init (chosenScale l.length))) with
      | none =>
        simpa [(outerRun_fields n Q cap init advance l).2.2.1] using
          And.intro (fallbackRun_matching l) (fallbackRun_subset l)
      | some P => exact hengine _ hm P ha
    · have he : selectedAnswer n Q answer (outerRun n Q cap init advance l)=none := by
        simp [selectedAnswer,(outerRun_fields n Q cap init advance l).1,hm]
      rw [he]
      simpa [(outerRun_fields n Q cap init advance l).2.2.1] using
        And.intro (fallbackRun_matching l) (fallbackRun_subset l)

/-- The EOF wrapper loses no value from a valid answer of its selected copy,
including when the complete-prefix exact branch wins instead. -/
theorem outerOutput_dominates_selected (n Q cap : ℕ) (init : ℕ→A)
    (advance : ℕ→A→Edge V→A) (answer : ℕ→A→Option (Graph V))
    (w : Edge V→ℕ) (l : List (Edge V)) (P : Graph V)
    (hm : chosenScale l.length∈scales n Q)
    (ha : answer (chosenScale l.length) (l.foldl (advance (chosenScale l.length))
      (init (chosenScale l.length)))=some P)
    (hP : Matching P) (hsub : P⊆l.toFinset) :
    (∑e∈P,(w e:ℝ)) ≤
      ∑e∈outerOutput n Q w answer (outerRun n Q cap init advance l),(w e:ℝ) := by
  by_cases hl : l.length≤cap
  · rw [outerOutput_full_exact n Q cap init advance answer w l hl,decode_real_weight,
      opt_eq_natOpt]
    exact_mod_cast matching_weight_le_natOpt w hsub hP
  · rw [outerOutput_overflow_selected n Q cap init advance answer w l (by omega) hm,ha]
    simp

def bufferRecords {E : Type*} : Option (List E) → ℕ
  | none => 0
  | some b => b.length

def outerRecordCount (n Q : ℕ) (record : A→ℕ) (s : OuterState V A n Q) : ℕ :=
  bufferRecords s.complete+s.fallback.card+∑M:ScaleIndex n Q,record (s.copies M)

theorem outerRecordCount_bound (n Q cap : ℕ) (init : ℕ→A)
    (advance : ℕ→A→Edge V→A) (l : List (Edge V)) (record : A→ℕ) (R : ℕ)
    (hr : ∀M:ScaleIndex n Q,record (l.foldl (advance M.val) (init M.val))≤R) :
    outerRecordCount n Q record (outerRun n Q cap init advance l) ≤
      cap+Fintype.card V/2+(Nat.log 2 (n*n)+1)*R := by
  have hbuf : bufferRecords (bufferRun cap l)≤cap := by
    cases hb : bufferRun cap l with
    | none => exact Nat.zero_le _
    | some b => exact bufferRun_hard_cap cap l b hb
  have hsum : (∑M:ScaleIndex n Q,record (l.foldl (advance M.val) (init M.val))) ≤
      (Nat.log 2 (n*n)+1)*R := by
    calc
      _ ≤ ∑_M:ScaleIndex n Q,R := Finset.sum_le_sum (fun M _ => hr M)
      _ = (scales n Q).card*R := by simp [ScaleIndex]
      _ ≤ _ := Nat.mul_le_mul_right _ (scales_count n Q)
  unfold outerRecordCount
  simp only [(outerRun_fields n Q cap init advance l).2.1,
    (outerRun_fields n Q cap init advance l).2.2.1,
    (outerRun_fields n Q cap init advance l).2.2.2]
  have hf := fallbackRun_cap l
  omega

end RobustMatching.R8StreamingWrapper
