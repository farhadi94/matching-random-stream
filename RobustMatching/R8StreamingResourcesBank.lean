import RobustMatching.R8StreamingWrapperConfigured
import RobustMatching.R8AcquisitionStateBasic
import RobustMatching.R8AcquisitionProvenance

/-! Storage of the actual materialized phase bank. This deliberately counts
every host graph separately. The sharper virtual-view representation is not
needed for the polynomial-logarithmic space guarantee. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingResources
open RobustMatching.R2Cut RobustMatching.R8StreamingWrapper
open RobustMatching.R7WeightedPhaseAssembly
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

def materializedBankRecords (s : BankState V) : ℕ :=
  s.shared.card + ∑ c ∈ reachedCuts s.count, (s.hosts c).card

theorem phase_card_le (w : Edge V → ℕ) (H : Graph V)
    (eligible : Edge V → Prop) (l : List (Edge V)) (c W : ℕ)
    (hw : ∀ e ∈ H ∪ l.toFinset, w e ≤ W) :
    (phaseFinal w H eligible l c).card ≤
      (sharedBase H eligible l).card + W * (Fintype.card V / 2) := by
  have hi := initial_subset_shared H eligible l c
  have hx := phase_owned_record_cap w H eligible l c W hw
  have hs : phaseFinal w H eligible l c ⊆ sharedBase H eligible l ∪
      (phaseFinal w H eligible l c \ initial H eligible l c) := by
    intro e he
    by_cases h : e ∈ initial H eligible l c
    · exact Finset.mem_union_left _ (hi h)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he,h⟩)
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hx _))

theorem materialized_bank_cap (w : Edge V → ℕ) (H : Graph V)
    (eligible : Edge V → Prop) (l : List (Edge V)) (W B : ℕ)
    (hw : ∀ e ∈ H ∪ l.toFinset, w e ≤ W)
    (hB : (sharedBase H eligible l).card ≤ B) :
    materializedBankRecords (bankRun w H eligible l) ≤
      B + cutoffCountBound l.length * (B + W * (Fintype.card V / 2)) := by
  unfold materializedBankRecords
  rw [bankRun_count,bankRun_shared]
  apply Nat.add_le_add hB
  calc
    (∑ c ∈ reachedCuts l.length, ((bankRun w H eligible l).hosts c).card)
      ≤ ∑ _c ∈ reachedCuts l.length, (B + W * (Fintype.card V / 2)) := by
        apply Finset.sum_le_sum
        intro c hc
        rw [bankRun_host,if_pos hc]
        exact (phase_card_le w H eligible l c W hw).trans (Nat.add_le_add_right hB _)
    _ = (reachedCuts l.length).card * (B + W * (Fintype.card V / 2)) := by simp
    _ ≤ cutoffCountBound l.length * (B + W * (Fintype.card V / 2)) :=
      Nat.mul_le_mul_right _ (reachedCuts_count l.length)

theorem cutoffCountBound_mono {a b : ℕ} (h : a ≤ b) :
    cutoffCountBound a ≤ cutoffCountBound b := by
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right h) _)

theorem buffer_records_cap (cap : ℕ) (l : List E) :
    bufferRecords (bufferRun cap l) ≤ cap := by
  rw [bufferRun_exact]
  split_ifs with h <;> simp [bufferRecords,h]

def suffixRecords (s : SuffixState V) : ℕ :=
  materializedBankRecords s.bank + bufferRecords s.complete

theorem suffix_records_cap (w : Edge V → ℕ) (H : Graph V)
    (eligible : Edge V → Prop) (l : List (Edge V)) (W B m : ℕ)
    (hw : ∀ e ∈ H ∪ l.toFinset, w e ≤ W)
    (hB : (sharedBase H eligible l).card ≤ B) (hl : l.length ≤ m) :
    suffixRecords (suffixRun w H eligible l) ≤
      B + cutoffCountBound m * (B + W * (Fintype.card V / 2)) + 10000000 := by
  unfold suffixRecords
  rw [(suffixRun_fields w H eligible l).1,(suffixRun_fields w H eligible l).2]
  apply Nat.add_le_add
  · exact (materialized_bank_cap w H eligible l W B hw hB).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (cutoffCountBound_mono hl)) _)
  · exact buffer_records_cap _ _

end RobustMatching.R8StreamingResources
