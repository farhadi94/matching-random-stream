import RobustMatching.R8StreamingResourcesLocal

noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingResources
open RobustMatching.R2Cut RobustMatching.R8StreamingWrapper
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false

def totalRecordBound (n N beta uCap W _Q cap m : ℕ) : ℕ :=
  cap + n / 2 + (Nat.log 2 (n*n) + 1) * localRecordBound N n beta uCap W m

/-- Every execution, including failed acquisition and overflow, satisfies the
bound. No approximation event or surviving-U assumption occurs here. -/
theorem bounded_integer_records (n Q cap : ℕ) (w : Edge V → ℕ)
    (configs : ℕ → R8Acquisition.Config) (model : R8Acquisition.BatchModel (Edge V) C)
    (l : List (Edge V)) (beta uCap W m : ℕ)
    (hn : n = Fintype.card V) (hb : ∀ M, (configs M).beta = beta)
    (hu : ∀ M, (configs M).uCap = uCap)
    (hw : ∀ e ∈ l, w e ≤ W) (hm : l.length ≤ m) :
    outerRecordCount n Q localRecords (boundedIntegerRun n Q cap w configs model l) ≤
      totalRecordBound n (Fintype.card C) beta uCap W Q cap m := by
  subst n
  change outerRecordCount (Fintype.card V) Q localRecords
    (outerRun (Fintype.card V) Q cap (fun _ => acquiredLocalInit)
      (fun M => acquiredLocalStep w (configs M) model) l) ≤
    cap + Fintype.card V / 2 + (Nat.log 2 (Fintype.card V * Fintype.card V)+1) *
      localRecordBound (Fintype.card C) (Fintype.card V) beta uCap W m
  apply outerRecordCount_bound (Fintype.card V) Q cap (fun _ => acquiredLocalInit)
    (fun M => acquiredLocalStep w (configs M) model) l localRecords
    (localRecordBound (Fintype.card C) (Fintype.card V) beta uCap W m)
  intro M
  simpa only [hb,hu] using local_records_cap (configs M.val) model w l W m hw hm

def configuredRecordBound (n N beta kappa LU L0 W : ℕ) : ℕ :=
  let Q := acquisitionBudget N beta
  totalRecordBound n N beta (copiedCapacity Q kappa LU) W Q
    (fullCapacity n Q kappa L0) (n*n)

/-- The actual configured one-pass state, with all predetermined dyadic copies
running from the first label. The input is a simple-graph stream. -/
theorem configured_records (w : Edge V → ℕ) (beta lower LU L0 W : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : R8Acquisition.BatchModel (Edge V) C) (l : List (Edge V))
    (hnd : l.Nodup) (hw : ∀ e ∈ l, w e ≤ W) :
    let Q := acquisitionBudget (Fintype.card C) beta
    let cfg := fun M => configForScale beta lower (copiedCapacity Q model.kappa LU) Q M hb hl
    outerRecordCount (Fintype.card V) Q localRecords
      (boundedIntegerRun (Fintype.card V) Q
        (fullCapacity (Fintype.card V) Q model.kappa L0) w cfg model l) ≤
      configuredRecordBound (Fintype.card V) (Fintype.card C) beta model.kappa LU L0 W := by
  dsimp only
  exact bounded_integer_records _ _ _ w _ model l beta _ W _ rfl
    (fun _ => rfl) (fun _ => rfl) hw (stream_length_le_square l hnd)


end RobustMatching.R8StreamingResources
