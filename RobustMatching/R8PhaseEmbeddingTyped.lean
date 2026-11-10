import RobustMatching.R8PhaseEmbeddingRecords
import RobustMatching.R8PhaseEmbeddingTypedChronology

/-! The actual repair labeling and physical clock bracket construct both
assembly records. No copied embedding, deletion-rank bound, selected-parent
chronology, or ordinary-support containment is an input. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open Classical
namespace RobustMatching.R8PhaseEmbedding
open R2Cut R7WeightedPhaseAssembly R7SupportFlowMap R7GraphBipartiteExchange
open R7ClosedRepair.TypedLabeling R7ClosedRepair.Typed R8RepairProbability
variable {V B : Type*} [Fintype V] [LinearOrder V] {q : ℕ}
variable (W : ℕ) (Mc : Graph (V×Fin W)) (hm : Matching Mc)
  (C : Finset (V×Fin W)) (available : Graph (V×Fin W))
  (bin : (V×Fin W)→Fin q) (mask : (V×Fin W)→Fin 4)
local notation "D" => coordinatesFromMatching Mc hm C available bin mask
local notation "lab" => actualVertexEquiv Mc hm C available bin mask
local instance : DecidableEq (CanonicalCenters D) := Classical.decEq _
local instance : DecidableEq (CanonicalOutsides D) := Classical.decEq _
local instance : DecidableEq (CanonicalVertex D) := Classical.decEq _

variable (w : Edge V→ℕ) (parent : Edge (V×Fin W)→Edge V)
  (original : B→Edge V) (par : Mc→B)
  (hpar : ∀e:Mc,parent e.val=original (par e))
  (H0 : Graph V) (eligible : Edge V→Prop) (stream : List (Edge V)) (cuts : Finset ℕ)
  (cut : Finset V) (z : B→Clock)
local notation "s" => states (fiberParents D par) z
local notation "adj" => actualReferenceAdj Mc hm C available bin mask
local notation "side" => fun v=>originalSide cut (Prod.fst (lab v))

def canonicalPhaseEmbedding (Hc : Graph (V×Fin W)) (a c t : ℕ)
    (hc : c∈activeCuts cuts stream) (hac : a≤c) (hct : c≤t)
    (hHcross : Crosses Hc (copyCut cut W)) (hMcross : Crosses Mc (copyCut cut W))
    (hHcopies : ConsistentCopies W w parent Hc) (hMcopies : ConsistentCopies W w parent Mc)
    (href : ∀e∈Hc,parent e∈H0)
    (hav : ∀e∈available,parent e∈H0 ∨ (eligible (parent e) ∧ parent e∈stream))
    (hbefore : ∀b,activeBit (z b)=true→ original b∈stream.take a)
    (hafter : ∀b,earlyBit (z b)=false→ original b∈stream.drop t) :
    @CopiedPhaseEmbedding V (CanonicalVertex D) _ (Classical.decEq _) w H0 eligible stream cuts
      (R7GraphMatrix.graphEdges fun c x=>adj Hc c x ∨ gateRelation s c x)
      (selectedEdges (P:=CenterUnmatched D) (I:=PairFiber D .internalAvailable)
        (U:=OutsideUnmatched D) s) side := by
  have hx : Crosses (Hc∪Mc) (copyCut cut W) := by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · exact hHcross e he
    · exact hMcross e he
  have hv : ConsistentCopies W w parent (Hc∪Mc) := by
    constructor
    · intro e he
      rcases Finset.mem_union.mp he with he|he
      · exact hHcopies.projection e he
      · exact hMcopies.projection e he
    · intro e he
      rcases Finset.mem_union.mp he with he|he
      · exact hHcopies.index e he
      · exact hMcopies.index e he
  have hA := actual_ordinary_subset Mc hm C available bin mask Hc s
  have hJ := actual_selected_subset Mc hm C available bin mask s
  exact phaseEmbedding w H0 eligible stream cuts cut W a c t hc hac hct parent lab (lab).injective
    _ _ (crosses_mono hx hA) (crosses_mono hMcross hJ) (hv.mono hA) (hMcopies.mono hJ)
    (typed_ordinary_initial Mc hm C available bin mask parent original par hpar
      H0 eligible stream z Hc a href hav hbefore)
    (typed_selected_chronology Mc hm C available bin mask parent original par hpar
      H0 eligible stream z t hav hafter)

/-- Pull back the full physical shared copied base through the already
constructed canonical cover/benchmark labeling. -/
def canonicalTypedBase : Graph (CanonicalVertex D) :=
  mapGraph (lab).symm (lab).symm.injective available

theorem canonicalTypedBase_image :
    mapGraph lab (lab).injective (canonicalTypedBase W Mc hm C available bin mask)=available := by
  exact mapGraph_equiv_symm (lab).symm available

theorem canonicalTypedBase_rank :
    rank (canonicalTypedBase W Mc hm C available bin mask)=rank available :=
  mapGraph_rank (lab).symm (lab).symm.injective available

/-- The full-base rank is the number of canonical centers, by the actual
minimum-cover identity. It is not a bound on any phase's initial host. -/
theorem canonicalTypedBase_center_rank (hminimum : rank available=C.card) :
    rank (canonicalTypedBase W Mc hm C available bin mask)=
      Fintype.card (CanonicalCenters D) := by
  rw [canonicalTypedBase_rank,hminimum,actual_center_card]

def canonicalBaseEmbedding
    (hcross : Crosses available (copyCut cut W))
    (hcopies : ConsistentCopies W w parent available)
    (hav : ∀e∈available,parent e∈H0 ∨ (eligible (parent e) ∧ parent e∈stream)) :
    @CopiedBaseEmbedding V (CanonicalVertex D) _ (Classical.decEq _) w H0 eligible stream cuts (canonicalTypedBase W Mc hm C available bin mask) := by
  apply baseEmbedding w H0 eligible stream cuts cut W parent lab (lab).injective
  · rw [canonicalTypedBase_image]
    exact hcross
  · rw [canonicalTypedBase_image]
    exact hcopies
  · rw [canonicalTypedBase_image]
    intro e he
    exact available_parent_shared available parent H0 eligible stream hav he

end RobustMatching.R8PhaseEmbedding
