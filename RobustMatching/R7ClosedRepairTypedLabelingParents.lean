import RobustMatching.R7ClosedRepairTypedLabeling
import RobustMatching.R7GraphDualBridge
import RobustMatching.R7CopyDualUnfold
import RobustMatching.R8RepairProbabilityReference

/-! Original parent labels for the actual canonical unfolded benchmark.
The random pair kinds form disjoint fibers of one actual matching. Each
original parent has at most W matching copies because their left copy
indices inject into Fin W. No copy-multiplicity premise is assumed. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Classical

namespace RobustMatching.R7ClosedRepair.TypedLabeling
open RobustMatching.R7SupportFlowMap RobustMatching.R2Cut
open RobustMatching.R7GraphMatrix RobustMatching.R7GraphDualBridge
open RobustMatching.R7CopyDual RobustMatching.R8RepairProbability

section Fibers
variable {B U O : Type*} [Fintype B] {q : ℕ}

def fiberParents (d : Coordinates B U q) (par : B → O) :
    Parents O (PairFiber d .gate) (PairFiber d .missing)
      (PairFiber d .internalMissing) (PairFiber d .root) where
  gate := fun g => par g.val
  missing := fun m => par m.val
  internalMissing := fun j => par j.val
  root := fun r => par r.val

lemma fiber_parent_sum (d : Coordinates B U q) (par : B → O) (b : O) (k : PairKind) :
    (∑ i : PairFiber d k, if par i.val = b then (1:ℝ) else 0) =
      ∑ i : B, if d.kind i = k then (if par i = b then (1:ℝ) else 0) else 0 := by
  symm
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro i; simp) _

theorem fiber_originalMultiplicity_le (d : Coordinates B U q) (par : B → O) (b : O) :
    originalMultiplicity (fiberParents d par) b ≤
      ∑ i : B, if par i = b then (1:ℝ) else 0 := by
  unfold originalMultiplicity fiberParents
  simp only [fiber_parent_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases hk : d.kind i <;> by_cases hp : par i = b <;> simp [hp]

end Fibers

section Copies
variable {L R U : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  {W q : ℕ}

def encodedCopyEquiv (S : Finset ((L × Fin W) × (R × Fin W))) :
    S ≃ encode S :=
  Equiv.ofBijective
    (fun e => ⟨edgeOf e.val, Finset.mem_image.mpr ⟨e.val,e.property,rfl⟩⟩) (by
      constructor
      · intro e f h
        exact Subtype.ext (edgeOf_injective (congrArg Subtype.val h))
      · intro e
        obtain ⟨p,hp,he⟩ := Finset.mem_image.mp e.property
        exact ⟨⟨p,hp⟩,Subtype.ext he⟩)

def encodedCopyParent (S : Finset ((L × Fin W) × (R × Fin W))) (e : encode S) : L × R :=
  parent ((encodedCopyEquiv S).symm e).val

theorem encodedCopyParent_edge (S : Finset ((L × Fin W) × (R × Fin W))) (e : S) :
    encodedCopyParent S (encodedCopyEquiv S e) = parent e.val := by
  simp only [encodedCopyParent, Equiv.symm_apply_apply]

/-- Distinct matching copies of one original edge have distinct left
copy indices. This uses the actual matching, not independent copy labels. -/
theorem encoded_parent_fiber_card_le
    (S : Finset ((L × Fin W) × (R × Fin W))) (hS : RobustMatching.Dual.IsMatching S)
    (b : L × R) :
    Fintype.card {e : encode S // encodedCopyParent S e = b} ≤ W := by
  let f : {e : encode S // encodedCopyParent S e = b} → Fin W :=
    fun e => ((encodedCopyEquiv S).symm e.val).val.1.2
  have hinj : Function.Injective f := by
    intro e g he
    apply Subtype.ext
    apply (encodedCopyEquiv S).symm.injective
    apply Subtype.ext
    apply hS.1 ((encodedCopyEquiv S).symm e.val).property
      ((encodedCopyEquiv S).symm g.val).property
    apply Prod.ext
    · exact (congrArg Prod.fst e.property).trans (congrArg Prod.fst g.property).symm
    · exact he
  simpa using Fintype.card_le_of_injective f hinj

theorem copied_originalMultiplicity_le
    (S : Finset ((L × Fin W) × (R × Fin W))) (hS : RobustMatching.Dual.IsMatching S)
    (d : Coordinates (encode S) U q) (b : L × R) :
    originalMultiplicity (fiberParents d (encodedCopyParent S)) b ≤ (W:ℝ) := by
  apply (fiber_originalMultiplicity_le d (encodedCopyParent S) b).trans
  have hcard := encoded_parent_fiber_card_le S hS b
  have heq : (∑ i : encode S, if encodedCopyParent S i = b then (1:ℝ) else 0) =
      Fintype.card {e : encode S // encodedCopyParent S e = b} := by
    simp [Fintype.card_subtype]
  have hle : (Fintype.card {e : encode S // encodedCopyParent S e = b} : ℝ) ≤ W := by
    exact_mod_cast hcard
  convert heq.le.trans hle using 1
  apply Finset.sum_congr rfl
  intro i _
  exact (ite_eq_ite _ _ _).mpr trivial

end Copies

section Canonical
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  (W : ℕ) (M : Finset (L × R)) (w : L × R → ℕ)
  (hm : RobustMatching.Dual.IsMatching M) {q : ℕ}

include hm in
theorem unfoldedBenchmarkMatching : Matching (encode (fullCopies W M w)) :=
  (encode_matching_iff _).mpr (fullCopies_matching W M w hm)

local notation "K" => encode (fullCopies W M w)

variable (C : Finset ((L × Fin W) ⊕ (R × Fin W))) (available : Graph ((L × Fin W) ⊕ (R × Fin W)))
  (bin : ((L × Fin W) ⊕ (R × Fin W)) → Fin q)
  (mask : ((L × Fin W) ⊕ (R × Fin W)) → Fin 4)

local notation "D" => coordinatesFromMatching K (unfoldedBenchmarkMatching W M w hm) C available bin mask

def canonicalCopyParents :
    Parents (L × R) (PairFiber D .gate) (PairFiber D .missing)
      (PairFiber D .internalMissing) (PairFiber D .root) :=
  fiberParents D (encodedCopyParent (fullCopies W M w))

/-- The probability packet's single multiplicity premise follows from
the actual canonical unfolding and the actual pair-kind classification. -/
theorem canonical_originalMultiplicity_le (b : L × R) :
    originalMultiplicity (canonicalCopyParents W M w hm C available bin mask) b ≤ (W:ℝ) :=
  copied_originalMultiplicity_le (fullCopies W M w) (fullCopies_matching W M w hm) D b

theorem canonical_pair_fibers_le (b : L × R) :
    (Finset.univ.filter fun g =>
      (canonicalCopyParents W M w hm C available bin mask).gate g = b).card ≤ W ∧
    (Finset.univ.filter fun m =>
      (canonicalCopyParents W M w hm C available bin mask).missing m = b).card ≤ W ∧
    (Finset.univ.filter fun j =>
      (canonicalCopyParents W M w hm C available bin mask).internalMissing j = b).card ≤ W ∧
    (Finset.univ.filter fun r =>
      (canonicalCopyParents W M w hm C available bin mask).root r = b).card ≤ W :=
  by
    convert pair_fibers_le _ W
      (canonical_originalMultiplicity_le W M w hm C available bin mask) b using 1
    all_goals exact Iff.of_eq (by congr)

/-- Instantiation of the existing local/count fiber interface. Only the
ordinary deterministic capped-support hypotheses remain; original-copy
multiplicity and local row/column block bounds are discharged here. -/
def canonicalReferenceLocalData (b0 : L × R) (hW : 0 < W)
    (H : CanonicalCenters D → CanonicalOutsides D → Prop)
    (sideC : CanonicalCenters D → Bool) (sideO : CanonicalOutsides D → Bool)
    (hcross : ∀ c x, H c x → sideC c ≠ sideO x)
    (β : ℝ) (a : CanonicalOutsides D → ℝ) (dc : CanonicalCenters D → ℝ)
    (hs : RobustMatching.R1Gate.SupportData (fun x c => H c x) β a dc) :
    LocalData (B := L × R) (G := PairFiber D .gate) (M := PairFiber D .missing)
      (P := CenterUnmatched D) (I := PairFiber D .internalAvailable)
      (J := PairFiber D .internalMissing) (R := PairFiber D .root) (U := OutsideUnmatched D) :=
  referenceLocalData (canonicalCopyParents W M w hm C available bin mask) b0
    H sideC sideO hcross β a dc hs W hW
    (canonical_originalMultiplicity_le W M w hm C available bin mask)

end Canonical
end RobustMatching.R7ClosedRepair.TypedLabeling
