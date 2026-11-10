import RandomOrderMatching.Phases.Execution.Certificates
import RandomOrderMatching.Analysis.Repair.Typed.Profile

/-! The actual typed repair profile is compiled into the actual matching
returned by the original-edge bank. Remaining premises are explicit
canonical labeling/minimum-cover data and the local/aggregate finite
probability events; no whole-profile or output-approximation premise. -/
noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Phases.Execution
open RandomOrderMatching.Graph RandomOrderMatching.Graph.MarkedPair
open RandomOrderMatching.Analysis.Repair RandomOrderMatching.Analysis.Repair.Typed
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G M P I J R U : Type*}
variable [Fintype G] [Fintype M] [Fintype P] [Fintype I]
  [Fintype J] [Fintype R] [Fintype U]

/-- Exact identification of the typed deleted graph used in its matching
construction with the selected-endpoint deletion used by the compiler. -/
theorem typed_deletion_identification
    (s : States G M J R)
    (A : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool) (layer : Bool) :
    RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s A sideC sideO layer) =
      deleteVertices (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (fun c x => A c x ∨ gateRelation s c x))
        ((covered (selectedEdges (P := P) (I := I) (U := U) s)).filter
          (fun v => Sum.elim sideC sideO v = layer)) := by
  rw [deletion_graph_eq,deletionVertices_eq_selected]
  rfl

/-- All actual phase/clock/deletion obligations are discharged from the
explicit copied embedding; selectedEdges_matching is a proved fact. -/
theorem typed_transfer_from_execution
    (w0 : Edge V → ℕ) (H0 : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ)
    (s : States G M J R)
    (A : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (Q : CopiedPhaseEmbedding w0 H0 eligible stream cuts
      (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (fun c x => A c x ∨ gateRelation s c x))
      (selectedEdges (P := P) (I := I) (U := U) s) (Sum.elim sideC sideO)) :
    (rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s A sideC sideO false)) : ℝ) +
      rank (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s A sideC sideO true)) +
      (selectedEdges (P := P) (I := I) (U := U) s).card ≤
      2 * ∑ e ∈ outputMatching w0 H0 eligible stream cuts, (w0 e : ℝ) := by
  classical
  rw [typed_deletion_identification,typed_deletion_identification]
  exact Q.transfer (selectedEdges_matching s)

/-- Compiler endpoint: the profile lower bound holds for the concrete
output matching. `hbaseRank` is the equality certified by the minimum
cover of the full analytic copied base, never a phase initial bound. -/
theorem typed_profile_from_execution
    (w0 : Edge V → ℕ) (H0 : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ)
    (s : States G M J R) (α ω : ℝ) (ha : α < 1) (hω : 0 < ω)
    (A : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (Q : CopiedPhaseEmbedding w0 H0 eligible stream cuts
      (RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (fun c x => A c x ∨ gateRelation s c x))
      (selectedEdges (P := P) (I := I) (U := U) s) (Sum.elim sideC sideO))
    (Base : Graph (Centers G M P I J ⊕ Outsides R M G U))
    (Qbase : CopiedBaseEmbedding w0 H0 eligible stream cuts Base)
    (hbaseRank : rank Base = Fintype.card (Centers G M P I J))
    (support : Centers G M P I J → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ support c x)
    (errC : Bool → Centers G M P I J → ℝ)
    (errO : Bool → Outsides R M G U → ℝ)
    (heC : ∀ layer c, 0 ≤ errC layer c) (heO : ∀ layer x, 0 ≤ errO layer x)
    (hlC : ∀ layer c,
      rowLoad (rawSupport s A sideC sideO support (normalizer α ω sideO) layer) c ≤
        1 + errC layer c)
    (hlO : ∀ layer x, ¬lowUnmatched support x → liveReceiver s sideO layer x →
      meanLoad α ω support sideO layer x / capacity α ω sideO layer x - errO layer x ≤
        colLoad (rawSupport s A sideC sideO support (normalizer α ω sideO) layer) x)
    (noiseG noiseR noiseM noiseJ noiseAvailability : ℝ)
    (hG : α * (Fintype.card G : ℝ) - noiseG ≤
      ∑ g, if s.active g = true then (1 : ℝ) else 0)
    (hR : (1-ω) * (Fintype.card R : ℝ) - noiseR ≤
      ∑ r, if s.earlyR r = false then (1 : ℝ) else 0)
    (hM : (1-ω) * (Fintype.card M : ℝ) - noiseM ≤
      ∑ m, if s.earlyM m = false then (1 : ℝ) else 0)
    (hJ : (1-ω) * (Fintype.card J : ℝ) - noiseJ ≤
      ∑ j, if s.earlyJ j = false then (1 : ℝ) else 0)
    (hAvailability : outsideProfile α ω support - noiseAvailability ≤
      ∑ layer : Bool, ∑ x, mixedValue s α ω A sideC sideO support layer x) :
    max (Fintype.card (Centers G M P I J) : ℝ)
      (profile α ω support -
        totalError errC errO noiseG noiseR noiseM noiseJ noiseAvailability / 2) ≤
      ∑ e ∈ outputMatching w0 H0 eligible stream cuts, (w0 e : ℝ) := by
  classical
  have hb := Qbase.rank_le_output
  rw [hbaseRank] at hb
  exact actual_profile_bound s α ω ha hω A sideC sideO support hw errC errO heC heO hlC hlO
    noiseG noiseR noiseM noiseJ noiseAvailability _ hG hR hM hJ hAvailability
    (typed_transfer_from_execution w0 H0 eligible stream cuts s A sideC sideO Q) hb

end RandomOrderMatching.Phases.Execution
#print axioms RandomOrderMatching.Phases.Execution.typed_transfer_from_execution
#print axioms RandomOrderMatching.Phases.Execution.typed_profile_from_execution
