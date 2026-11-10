import RobustMatching.R8AcquisitionPotential

/-! A deterministic finite cleanup loop. Its fuel is proved sufficient
from actual graph potential, not an assumed termination theorem. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical
namespace RobustMatching.R8Acquisition
open RobustMatching.R2Cut
variable {V : Type*} [Fintype V] [DecidableEq V]

def firstEdge (S : Graph V) (hS : S.Nonempty) : Edge V :=
  (S.exists_min_image (fun e => (Fintype.equivFin (Edge V) e).val) hS).choose

theorem firstEdge_mem (S : Graph V) (hS : S.Nonempty) : firstEdge S hS ∈ S :=
  (S.exists_min_image (fun e => (Fintype.equivFin (Edge V) e).val) hS).choose_spec.1

theorem firstEdge_min (S : Graph V) (hS : S.Nonempty) (e : Edge V) (he : e ∈ S) :
    (Fintype.equivFin (Edge V) (firstEdge S hS)).val ≤ (Fintype.equivFin (Edge V) e).val :=
  (S.exists_min_image (fun e => (Fintype.equivFin (Edge V) e).val) hS).choose_spec.2 e he

def badEdges (beta : ℕ) (H : Graph V) : Graph V := H.filter (fun e => beta<edgeDegree H e)

theorem badEdges_nonempty (beta : ℕ) (H : Graph V) (h : ¬Upper beta H) :
    (badEdges beta H).Nonempty := by
  unfold Upper at h
  push Not at h
  obtain ⟨e,he,hbad⟩ := h
  exact ⟨e,Finset.mem_filter.mpr ⟨he,hbad⟩⟩

def firstBad (beta : ℕ) (H : Graph V) (h : ¬Upper beta H) : Edge V :=
  firstEdge (badEdges beta H) (badEdges_nonempty beta H h)

theorem firstBad_spec (beta : ℕ) (H : Graph V) (h : ¬Upper beta H) :
    firstBad beta H h ∈ H ∧ beta<edgeDegree H (firstBad beta H h) :=
  Finset.mem_filter.mp (firstEdge_mem (badEdges beta H) (badEdges_nonempty beta H h))

def cleanupFuel (beta : ℕ) : ℕ → Graph V → Graph V
  | 0,H => H
  | n+1,H => if h : Upper beta H then H else cleanupFuel beta n (H.erase (firstBad beta H h))

def operationBound (beta : ℕ) : ℕ := Fintype.card V*beta^2+1

def cleanup (beta : ℕ) (H : Graph V) : Graph V := cleanupFuel beta (operationBound (V := V) beta) H

theorem cleanupFuel_subset (beta n : ℕ) (H : Graph V) : cleanupFuel beta n H ⊆ H := by
  induction n generalizing H with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    simp only [cleanupFuel]
    split_ifs
    · exact Finset.Subset.refl _
    · exact (ih _).trans (Finset.erase_subset _ _)

theorem cleanupFuel_stable (beta n : ℕ) (H : Graph V) (hH : Upper beta H) :
    cleanupFuel beta n H=H := by
  cases n <;> simp [cleanupFuel,hH]

theorem cleanupFuel_potential (beta n : ℕ) (H : Graph V) :
    potential beta H ≤ potential beta (cleanupFuel beta n H) := by
  induction n generalizing H with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [cleanupFuel]
    split_ifs with hh
    · exact le_rfl
    · have hp := erase_potential_increase beta (firstBad beta H hh)
        (firstBad_spec beta H hh).1 (firstBad_spec beta H hh).2
      have hi := ih (H.erase (firstBad beta H hh))
      linarith

theorem cleanupFuel_failure_progress (beta n : ℕ) (H : Graph V)
    (hbad : ¬Upper beta (cleanupFuel beta n H)) :
    potential beta H+(n : ℤ) ≤ potential beta (cleanupFuel beta n H) := by
  induction n generalizing H with
  | zero => simp [cleanupFuel]
  | succ n ih =>
    by_cases hh : Upper beta H
    · have hok : Upper beta (cleanupFuel beta (n+1) H) := by
        rw [cleanupFuel_stable beta (n+1) H hh]
        exact hh
      exact False.elim (hbad hok)
    · rw [cleanupFuel,dif_neg hh] at hbad ⊢
      have hp := erase_potential_increase beta (firstBad beta H hh)
        (firstBad_spec beta H hh).1 (firstBad_spec beta H hh).2
      have hi := ih (H.erase (firstBad beta H hh)) hbad
      push_cast
      linarith

theorem cleanup_upper (beta : ℕ) (H : Graph V) (hp : 0≤potential beta H) :
    Upper beta (cleanup beta H) := by
  by_contra hh
  have hprog := cleanupFuel_failure_progress beta (operationBound (V := V) beta) H hh
  have hbound := potential_upper beta (cleanup beta H)
  change potential beta H+(operationBound (V := V) beta : ℤ) ≤ potential beta (cleanup beta H) at hprog
  simp only [operationBound,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one] at hprog
  linarith

theorem cleanup_subset (beta : ℕ) (H : Graph V) : cleanup beta H ⊆ H :=
  cleanupFuel_subset beta _ H

theorem cleanup_potential (beta : ℕ) (H : Graph V) :
    potential beta H ≤ potential beta (cleanup beta H) := cleanupFuel_potential beta _ H

end RobustMatching.R8Acquisition
#print axioms RobustMatching.R8Acquisition.cleanup_upper
