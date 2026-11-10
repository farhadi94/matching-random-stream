import RandomOrderMatching.Phases.Execution.CopyTransfer
import RandomOrderMatching.Phases.Execution.DeletionMaps

/-! Explicit structural interfaces for canonical copied repair graphs.
The fields describe vertices, edges, cut sides and actual arrival labels;
none is a deletion-rank inequality or an approximation premise. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Phases.Execution
open RandomOrderMatching.Graph RandomOrderMatching.Graph.MarkedPair
open RandomOrderMatching.Graph.BipartiteDual RandomOrderMatching.Unfolding.Covers
open RandomOrderMatching.HistoricalDeletion.CutEncoding
variable {V T : Type*} [Fintype V] [LinearOrder V] [DecidableEq T]

structure CopiedPhaseEmbedding
    (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (A J : Graph T) (side : T → Bool) where
  cut : Finset V
  W : ℕ
  a : ℕ
  c : ℕ
  t : ℕ
  active : c ∈ activeCuts cuts stream
  before : a ≤ c
  after : c ≤ t
  E : Finset (Left cut × Right cut)
  P : Finset (Left cut × Right cut)
  early : encode cut E ⊆ initial H eligible stream a
  chronology : ∀ e ∈ encode cut P, e ∈ sharedBase H eligible stream ∨ e ∈ stream.drop t
  B : Finset ((Left cut × Fin W) × (Right cut × Fin W))
  S : Finset ((Left cut × Fin W) × (Right cut × Fin W))
  ordinaryCopies : ∀ e ∈ B, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p))
  selectedParents : ∀ e ∈ S, RandomOrderMatching.Unfolding.parent e ∈ P
  selectedIndex : ∀ e ∈ S, e.1.2.val+e.2.2.val+1=w (edgeOf cut (RandomOrderMatching.Unfolding.parent e))
  label : T → (Left cut × Fin W) ⊕ (Right cut × Fin W)
  injective : Function.Injective label
  side_eq : ∀ v, copySide (label v) = side v
  ordinary : mapGraph label injective A ⊆ RandomOrderMatching.Graph.BipartiteEncoding.encode B
  selected : mapGraph label injective J = RandomOrderMatching.Graph.BipartiteEncoding.encode S

/-- Structural edge/clock data imply the transfer inequality for actual
source graph ranks and the concrete output matching. -/
theorem CopiedPhaseEmbedding.transfer
    {w : Edge V → ℕ} {H : Graph V} {eligible : Edge V → Prop}
    {stream : List (Edge V)} {cuts : Finset ℕ} {A J : Graph T} {side : T → Bool}
    (Q : CopiedPhaseEmbedding w H eligible stream cuts A J side) (hJ : Matching J) :
    (rank (deleteVertices A ((covered J).filter (fun v => side v = false))) : ℝ) +
      rank (deleteVertices A ((covered J).filter (fun v => side v = true))) + J.card ≤
      2 * ∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ) := by
  exact bank_relabelled_copy_transfer w H eligible stream cuts Q.a Q.c Q.t
    Q.active Q.before Q.after Q.cut Q.W Q.E Q.P Q.early Q.chronology
    Q.B Q.S Q.ordinaryCopies Q.selectedParents Q.selectedIndex Q.label Q.injective
    _ _ J hJ Q.selected
    (relabelled_deletion_left Q.label Q.injective A J Q.B Q.S Q.ordinary Q.selected side Q.side_eq)
    (relabelled_deletion_right Q.label Q.injective A J Q.B Q.S Q.ordinary Q.selected side Q.side_eq)

structure CopiedBaseEmbedding
    (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (A : Graph T) where
  cut : Finset V
  W : ℕ
  E : Finset (Left cut × Right cut)
  parents : encode cut E ⊆ sharedBase H eligible stream
  B : Finset ((Left cut × Fin W) × (Right cut × Fin W))
  copies : ∀ e ∈ B, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p))
  label : T → (Left cut × Fin W) ⊕ (Right cut × Fin W)
  injective : Function.Injective label
  embedding : mapGraph label injective A ⊆ RandomOrderMatching.Graph.BipartiteEncoding.encode B

theorem CopiedBaseEmbedding.rank_le_output
    {w : Edge V → ℕ} {H : Graph V} {eligible : Edge V → Prop}
    {stream : List (Edge V)} {cuts : Finset ℕ} {A : Graph T}
    (Q : CopiedBaseEmbedding w H eligible stream cuts A) :
    (rank A : ℝ) ≤ ∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ) :=
  bank_relabelled_base_bound w H eligible stream cuts Q.cut Q.W Q.E Q.parents Q.B Q.copies
    Q.label Q.injective A Q.embedding

end RandomOrderMatching.Phases.Execution
#print axioms RandomOrderMatching.Phases.Execution.CopiedPhaseEmbedding.transfer
#print axioms RandomOrderMatching.Phases.Execution.CopiedBaseEmbedding.rank_le_output
