import RandomOrderMatching.Resources.WeightWindows
import RandomOrderMatching.Resources.PolynomialBound
import RandomOrderMatching.Streaming.BoundedMachine

/-! The final canonical, clamped machine: no arbitrary copy model or local
space contract remains in these resource conclusions. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Resources
open RandomOrderMatching.Graph RandomOrderMatching.Streaming
open RandomOrderMatching.Acquisition RandomOrderMatching.Weights.Windows
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

theorem canonical_machine_records (W L LU L0 : ℕ) (hW : 0 < W) (hL : 0 < L)
    (w : Edge V → ℕ) (l : List (Edge V)) (hnd : l.Nodup) :
    outerRecordCount (Fintype.card V) (canonicalBudget V W L) localRecords
      ((canonicalMachine W L LU L0 hW hL).run w l) ≤
      configuredRecordBound (Fintype.card V) (Fintype.card V*W)
        (10^30*W*L) W LU L0 W := by
  by_cases h : Nonempty (Edge V)
  · simp only [Machine.run,canonicalMachine,dif_pos h]
    have hh := bounded_integer_records (Fintype.card V) (canonicalBudget V W L)
      (fullCapacity (Fintype.card V) (canonicalBudget V W L) W L0)
      (clippedWeight w W)
      (fun M => finalScaleConfig W L (canonicalBudget V W L)
        (copiedCapacity (canonicalBudget V W L) W LU) M hW hL)
      (canonicalBatchModel W (clippedWeight w W) (clippedWeight_le w W) (Classical.choice h))
      l (10^30*W*L) (copiedCapacity (canonicalBudget V W L) W LU) W
      (Fintype.card V*Fintype.card V) rfl (fun _ => rfl) (fun _ => rfl)
      (fun e _ => clippedWeight_le w W e) (stream_length_le_square l hnd)
    simpa only [boundedIntegerRun,outerRun,configuredRecordBound,canonicalBudget,
      canonical_copied_vertex_count] using hh
  · have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons e es => exact (h ⟨e⟩).elim
    subst l
    simp [Machine.run,canonicalMachine,outerInit,outerRecordCount,bufferRecords,
      acquiredLocalInit,localRecords,initialState]

theorem window_integer_range_pos (p : Parameters) : 0 < p.integerRange := by
  apply Nat.ceil_pos.mpr
  exact div_pos (pow_pos (lt_trans zero_lt_one p.base_gt_one) _) p.eta_pos

theorem canonical_machine_records_polynomial (W L LU L0 K : ℕ)
    (hW : 0 < W) (hL : 0 < L) (w : Edge V → ℕ) (l : List (Edge V))
    (hnd : l.Nodup) (hn : 1 ≤ Fintype.card V)
    (hLK : L ≤ K) (hUK : LU ≤ K) (h0K : L0 ≤ K)
    (hlog : Nat.log 2 (Fintype.card V * Fintype.card V)+1 ≤ K) :
    outerRecordCount (Fintype.card V) (canonicalBudget V W L) localRecords
      ((canonicalMachine W L LU L0 hW hL).run w l) ≤
      10^77 * Fintype.card V * W^4 * K^5 := by
  apply (canonical_machine_records W L LU L0 hW hL w l hnd).trans
  have hh := configured_records_polynomial (Fintype.card V) (Fintype.card V*W)
    (10^30*W*L) W LU L0 W (10^30) K hn (by omega) (by omega) le_rfl
    (Nat.mul_le_mul_left (10^30*W) hLK) (by norm_num) le_rfl hUK h0K hlog
  have he : (100000000000000000 : ℕ) * (10^30)^2 = 10^77 := by norm_num
  rw [he] at hh
  exact hh

/-- The actual arbitrary-rational dictionary, instantiated with the final
canonical clamped streaming machine. This theorem needs no input weight bound. -/
theorem canonical_window_records (p : Parameters) (L LU L0 : ℕ) (hL : 0 < L)
    (w : Edge V → ℚ) (stream : ℕ → Edge V) (t : ℕ)
    (hw : ∀ e, 0 < w e) (hnd : (streamList stream t).Nodup)
    (hn : 0 < Fintype.card V) :
    dictionaryRecords p (canonicalMachine p.integerRange L LU L0 (window_integer_range_pos p) hL)
      (outerRecordCount (Fintype.card V) (canonicalBudget V p.integerRange L) localRecords)
      w (Fintype.card V) stream t ≤
      (p.k+p.liveExponent (Fintype.card V)+1) *
        configuredRecordBound (Fintype.card V) (Fintype.card V*p.integerRange)
          (10^30*p.integerRange*L) p.integerRange LU L0 p.integerRange := by
  apply dictionary_records_cap p _ _ w (Fintype.card V) stream t
    (p.liveExponent (Fintype.card V)) _ hw (p.liveExponent_spec (Fintype.card V) hn)
  intro j
  exact canonical_machine_records p.integerRange L LU L0 (window_integer_range_pos p) hL
    (p.integerWeight w j) (p.localList w j (streamList stream t)) (hnd.filter _)

end RandomOrderMatching.Resources
