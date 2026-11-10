import RobustMatching.R7ClosedRepairTypedLabelingParents
import RobustMatching.R7ClosedRepairTypedLabelingActual
import RobustMatching.R7GraphKonig

/-! Canonical graph-level cover and original-parent multiplicity facts.
Neither a minimum cover nor independent copies are supplied as premises. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RobustMatching.R8FixedHost
open R2Cut R7ClosedRepair.TypedLabeling R7SupportFlowMap R8RepairProbability

variable {V B : Type*} [Fintype V] [DecidableEq V]

def minimumCover (A : Graph V) (hA : (R7GraphKonig.simpleGraph A).Colorable 2) : Finset V :=
  Classical.choose (Classical.choose_spec (R7GraphKonig.project_konig A hA))

theorem minimumCover_spec (A : Graph V) (hA : (R7GraphKonig.simpleGraph A).Colorable 2) :
    (∀e∈A,(e.val∩minimumCover A hA).Nonempty) ∧
      (minimumCover A hA).card=rank A := by
  have h := Classical.choose_spec (Classical.choose_spec (R7GraphKonig.project_konig A hA))
  exact ⟨h.2.2.1,h.2.2.2.2⟩

theorem canonical_randomPairCount_le {q : ℕ}
    (M : Graph V) (hM : Matching M) (C : Finset V) (A : Graph V)
    (bin : V→Fin q) (mask : V→Fin 4) :
    let d := coordinatesFromMatching M hM C A bin mask
    randomPairCount (PairFiber d .gate) (PairFiber d .missing)
      (PairFiber d .internalMissing) (PairFiber d .root)≤(M.card:ℝ) := by
  dsimp only
  have h := actual_benchmark_card M hM C A bin mask
  simp only [CanonicalBenchmark,R7ClosedRepair.Typed.Benchmarks,Fintype.card_sum] at h
  unfold randomPairCount
  have hh : (Fintype.card (PairFiber (coordinatesFromMatching M hM C A bin mask)
    .internalAvailable):ℝ)≥0 := Nat.cast_nonneg _
  exact_mod_cast (by omega :
    Fintype.card (PairFiber (coordinatesFromMatching M hM C A bin mask) .gate)+
    Fintype.card (PairFiber (coordinatesFromMatching M hM C A bin mask) .missing)+
    Fintype.card (PairFiber (coordinatesFromMatching M hM C A bin mask) .internalMissing)+
    Fintype.card (PairFiber (coordinatesFromMatching M hM C A bin mask) .root)≤M.card)

/-- A matching contains at most W copies with one prescribed original
endpoint. This works on the actual unsplit copied vertex set. -/
theorem parent_fiber_le {W : ℕ} (M : Graph (V×Fin W)) (hM : Matching M)
    (par : M→B) (endpoint : B→V)
    (hend : ∀e:M,∃i:Fin W,(endpoint (par e),i)∈e.val.val) (b : B) :
    Fintype.card {e:M // par e=b}≤W := by
  let idx (e:M) : Fin W := Classical.choose (hend e)
  have hi (e:M) : (endpoint (par e),idx e)∈e.val.val := Classical.choose_spec (hend e)
  let f : {e:M // par e=b}→Fin W := fun e=>idx e.val
  have hf : Function.Injective f := by
    intro e g he
    apply Subtype.ext
    apply Subtype.ext
    by_contra hne
    have hd := hM e.val.property g.val.property hne
    have h1 := hi e.val
    have h2 := hi g.val
    rw [e.property] at h1
    rw [g.property] at h2
    change idx e.val=idx g.val at he
    rw [←he] at h2
    exact Finset.disjoint_left.mp hd h1 h2
  simpa using Fintype.card_le_of_injective f hf

theorem actual_originalMultiplicity_le {W q : ℕ}
    (M : Graph (V×Fin W)) (hM : Matching M) (C : Finset (V×Fin W))
    (A : Graph (V×Fin W)) (bin : (V×Fin W)→Fin q) (mask : (V×Fin W)→Fin 4)
    (par : M→B) (endpoint : B→V)
    (hend : ∀e:M,∃i:Fin W,(endpoint (par e),i)∈e.val.val) (b : B) :
    originalMultiplicity
      (fiberParents (coordinatesFromMatching M hM C A bin mask) par) b≤(W:ℝ) := by
  apply (fiber_originalMultiplicity_le (coordinatesFromMatching M hM C A bin mask) par b).trans
  have hc := parent_fiber_le M hM par endpoint hend b
  have heq : (∑e:M,if par e=b then (1:ℝ) else 0)=
      (Fintype.card {e:M //par e=b}:ℝ) := by simp [Fintype.card_subtype]
  rw [heq]
  exact_mod_cast hc

end RobustMatching.R8FixedHost
