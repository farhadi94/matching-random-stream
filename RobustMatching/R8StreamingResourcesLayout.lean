import RobustMatching.R8StreamingResourcesEncoding
import RobustMatching.R8StreamingResourcesCounters

/-! Actual finite-field counts for the proposed ordinary packed layout.
This is a count/encoding interface, not an extracted state serializer. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingResources
open RobustMatching.R2Cut RobustMatching.R8StreamingWrapper
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- Includes branch tags, array lengths, acquisition scalars, and at most four
scalar fields per actually reached phase. Eligible is derived from frozen H. -/
def localMetadata : LocalState (R8Acquisition.State C) V → ℕ
  | .aborted => 1
  | .acquiring _ => 16
  | .running _ _ sf => 16 + 4*(reachedCuts sf.bank.count).card

theorem local_metadata_cap (cfg : R8Acquisition.Config)
    (model : R8Acquisition.BatchModel (Edge V) C) (w : Edge V → ℕ)
    (l : List (Edge V)) (m : ℕ) (hm : l.length ≤ m) :
    localMetadata (l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit) ≤
      16 + 4*cutoffCountBound m := by
  have hi := local_run_invariant cfg model w l
  cases hs : l.foldl (acquiredLocalStep w cfg model) acquiredLocalInit with
  | aborted => simp only [localMetadata]; omega
  | acquiring a => simp only [localMetadata]; omega
  | running a view sf =>
    rw [hs] at hi
    obtain ⟨_,_,_,_,_,tail,htail,hsf⟩ := hi
    simp only [localMetadata,hsf,(suffixRun_fields w view.reference view.eligible tail).1,
      bankRun_count]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 4
      ((reachedCuts_count tail.length).trans (cutoffCountBound_mono (htail.length_le.trans hm)))) _

def outerMetadata (n Q : ℕ)
    (s : OuterState V (LocalState (R8Acquisition.State C) V) n Q) : ℕ :=
  16 + ∑ M : ScaleIndex n Q, localMetadata (s.copies M)

theorem actual_metadata_cap (n Q cap : ℕ) (w : Edge V → ℕ)
    (configs : ℕ → R8Acquisition.Config) (model : R8Acquisition.BatchModel (Edge V) C)
    (l : List (Edge V)) (hm : l.length ≤ n*n) :
    outerMetadata n Q (boundedIntegerRun n Q cap w configs model l) ≤ metadataWords n := by
  unfold outerMetadata metadataWords
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _M : ScaleIndex n Q, (16 + 4*cutoffCountBound (n*n)) := by
      apply Finset.sum_le_sum
      intro M _
      change localMetadata ((outerRun n Q cap (fun _ => acquiredLocalInit)
        (fun M => acquiredLocalStep w (configs M) model) l).copies M) ≤ _
      rw [(outerRun_fields n Q cap (fun _ => acquiredLocalInit)
        (fun M => acquiredLocalStep w (configs M) model) l).2.2.2]
      exact local_metadata_cap (configs M.val) model w l (n*n) hm
    _ = (scales n Q).card * (16 + 4*cutoffCountBound (n*n)) := by simp [ScaleIndex]
    _ ≤ _ := Nat.mul_le_mul_right _ (scales_count n Q)

def actualFieldLedger (n N W m Q counterBound : ℕ)
    (s : OuterState V (LocalState (R8Acquisition.State C) V) n Q) : ℕ :=
  outerRecordCount n Q localRecords s * recordBits n N W m +
    outerMetadata n Q s * wordBits (counterBound+1)

/-- Concrete field widths and both actual field counts compose. The theorem
does not assert existence of a packed reachable-state serializer or its space. -/
theorem configured_actual_field_ledger (w : Edge V → ℕ)
    (beta lower LU L0 W : ℕ) (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : R8Acquisition.BatchModel (Edge V) C) (l : List (Edge V))
    (hnd : l.Nodup) (hw : ∀ e ∈ l, w e ≤ W) :
    let n := Fintype.card V
    let N := Fintype.card C
    let Q := acquisitionBudget N beta
    let R := configuredRecordBound n N beta model.kappa LU L0 W
    let cfg := fun M => configForScale beta lower (copiedCapacity Q model.kappa LU) Q M hb hl
    actualFieldLedger n N W (n*n) Q (counterMax n N beta W R)
      (boundedIntegerRun n Q (fullCapacity n Q model.kappa L0) w cfg model l) ≤
      storageBitLedger R n N W (n*n) (counterMax n N beta W R) := by
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_right _ (configured_records w beta lower LU L0 W hb hl model l hnd hw)
  · exact Nat.mul_le_mul_right _ (actual_metadata_cap _ _ _ w _ model l
      (stream_length_le_square l hnd))

theorem metadata_words_polynomial (n L : ℕ) (hL : 1 ≤ L)
    (hlog : Nat.log 2 (n*n)+1 ≤ L) : metadataWords n ≤ 40000032 * L^2 := by
  have hP : cutoffCountBound (n*n) ≤ 10000000*L := Nat.mul_le_mul_left _ hlog
  have hm := Nat.mul_le_mul hlog (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hP) 16)
  have hs : L ≤ L^2 := by nlinarith only [hL]
  unfold metadataWords
  nlinarith only [hm,hs,hL]

end RobustMatching.R8StreamingResources
