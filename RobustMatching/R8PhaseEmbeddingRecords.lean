import RobustMatching.R8PhaseEmbeddingCoordinates

/-! Construct the frozen assembly records from actual unsplit copied
edge sets and their original parent identities. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RobustMatching.R8PhaseEmbedding
open R2Cut R7WeightedPhaseAssembly R7CopyDualGeneralBridge
open R7GraphBipartiteExchange R6FableSharpDualCopy
variable {V T : Type*} [Fintype V] [LinearOrder V] [DecidableEq T]

structure ConsistentCopies (W : ℕ) (w : Edge V→ℕ)
    (parent : Edge (V×Fin W)→Edge V) (A : Graph (V×Fin W)) : Prop where
  projection : ∀ e∈A,e.val.image Prod.fst=(parent e).val
  index : ∀ e∈A,∀ u∈e.val,∀ v∈e.val,u≠v→u.2.val+v.2.val+1=w (parent e)

theorem ConsistentCopies.mono {W : ℕ} {w : Edge V→ℕ}
    {parent : Edge (V×Fin W)→Edge V} {A B : Graph (V×Fin W)}
    (h : ConsistentCopies W w parent A) (hBA : B⊆A) : ConsistentCopies W w parent B :=
  ⟨fun e he=>h.projection e (hBA he),fun e he=>h.index e (hBA he)⟩

theorem physical_parent (C : Finset V) (W : ℕ) (p : CopyPair C W)
    (parent : Edge (V×Fin W)→Edge V)
    (h : (physicalEdge C W p).val.image Prod.fst=(parent (physicalEdge C W p)).val) :
    edgeOf C (R7CopyDual.parent p)=parent (physicalEdge C W p) := by
  apply Subtype.ext
  rw [←h,physicalEdge_val]
  simp [edgeOf,R7CopyDual.parent]

theorem physical_index (C : Finset V) (W : ℕ) (w : Edge V→ℕ)
    (parent : Edge (V×Fin W)→Edge V) (A : Graph (V×Fin W))
    (hA : ConsistentCopies W w parent A) (p : CopyPair C W)
    (hp : physicalEdge C W p∈A) :
    p.1.2.val+p.2.2.val+1=w (edgeOf C (R7CopyDual.parent p)) := by
  rw [physical_parent C W p parent (hA.projection _ hp)]
  apply hA.index _ hp (p.1.1.val,p.1.2) (by rw [physicalEdge_val]; simp)
    (p.2.1.val,p.2.2) (by rw [physicalEdge_val]; simp)
  intro hh
  have heq : p.1.1.val=p.2.1.val := congrArg Prod.fst hh
  exact p.2.1.property (heq ▸ p.1.1.property)

def originalPairs (C : Finset V) (E : Graph V) : Finset (Left C×Right C) :=
  Finset.univ.filter fun p=>edgeOf C p∈E

theorem encode_originalPairs_subset (C : Finset V) (E : Graph V) :
    encode C (originalPairs C E)⊆E := by
  intro e he
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
  exact (Finset.mem_filter.mp hp).2

/-- No copied embedding is assumed: the canonical cut labeling, ordinary
pairs, selected pairs and all antidiagonal conditions are constructed. -/
def phaseEmbedding
    (w : Edge V→ℕ) (H : Graph V) (eligible : Edge V→Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (C : Finset V) (W a c t : ℕ)
    (hc : c∈activeCuts cuts stream) (hac : a≤c) (hct : c≤t)
    (parent : Edge (V×Fin W)→Edge V) (f : T→V×Fin W) (hf : Function.Injective f)
    (A J : Graph T)
    (hAcross : Crosses (mapGraph f hf A) (copyCut C W))
    (hJcross : Crosses (mapGraph f hf J) (copyCut C W))
    (hA : ConsistentCopies W w parent (mapGraph f hf A))
    (hJ : ConsistentCopies W w parent (mapGraph f hf J))
    (hearly : ∀ e∈mapGraph f hf A,parent e∈initial H eligible stream a)
    (hlate : ∀ e∈mapGraph f hf J,
      parent e∈sharedBase H eligible stream ∨ parent e∈stream.drop t) :
    CopiedPhaseEmbedding w H eligible stream cuts A J (fun v=>originalSide C (f v).1) where
  cut := C
  W := W
  a := a
  c := c
  t := t
  active := hc
  before := hac
  after := hct
  E := originalPairs C (initial H eligible stream a)
  P := originalPairs C (sharedBase H eligible stream ∪ (stream.drop t).toFinset)
  early := encode_originalPairs_subset _ _
  chronology := by
    intro e he
    have hh := encode_originalPairs_subset _ _ he
    simpa only [Finset.mem_union,List.mem_toFinset] using hh
  B := copiedPairs C W (mapGraph f hf A)
  S := copiedPairs C W (mapGraph f hf J)
  ordinaryCopies := by
    intro p hp
    have hh := (mem_copiedPairs C W _ p).mp hp
    refine ⟨?_,physical_index C W w parent _ hA p hh⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change edgeOf C (R7CopyDual.parent p)∈initial H eligible stream a
    rw [physical_parent C W p parent (hA.projection _ hh)]
    exact hearly _ hh
  selectedParents := by
    intro p hp
    have hh := (mem_copiedPairs C W _ p).mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [physical_parent C W p parent (hJ.projection _ hh)]
    simpa only [Finset.mem_union,List.mem_toFinset] using hlate _ hh
  selectedIndex := by
    intro p hp
    exact physical_index C W w parent _ hJ p ((mem_copiedPairs C W _ p).mp hp)
  label := (copyLabel C W)∘f
  injective := (copyLabel C W).injective.comp hf
  side_eq := by intro v; exact copyLabel_side C W (f v)
  ordinary := by
    rw [←mapGraph_comp f hf (copyLabel C W) (copyLabel C W).injective A,copiedPairs_encode C W _ hAcross]
  selected := by
    rw [←mapGraph_comp f hf (copyLabel C W) (copyLabel C W).injective J,copiedPairs_encode C W _ hJcross]

def baseEmbedding
    (w : Edge V→ℕ) (H : Graph V) (eligible : Edge V→Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (C : Finset V) (W : ℕ)
    (parent : Edge (V×Fin W)→Edge V) (f : T→V×Fin W) (hf : Function.Injective f)
    (A : Graph T)
    (hcross : Crosses (mapGraph f hf A) (copyCut C W))
    (hA : ConsistentCopies W w parent (mapGraph f hf A))
    (hparents : ∀e∈mapGraph f hf A,parent e∈sharedBase H eligible stream) :
    CopiedBaseEmbedding w H eligible stream cuts A where
  cut := C
  W := W
  E := originalPairs C (sharedBase H eligible stream)
  parents := encode_originalPairs_subset _ _
  B := copiedPairs C W (mapGraph f hf A)
  copies := by
    intro p hp
    have hh := (mem_copiedPairs C W _ p).mp hp
    refine ⟨?_,physical_index C W w parent _ hA p hh⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change edgeOf C (R7CopyDual.parent p)∈sharedBase H eligible stream
    rw [physical_parent C W p parent (hA.projection _ hh)]
    exact hparents _ hh
  label := (copyLabel C W)∘f
  injective := (copyLabel C W).injective.comp hf
  embedding := by rw [←mapGraph_comp f hf (copyLabel C W) (copyLabel C W).injective A,copiedPairs_encode C W _ hcross]

end RobustMatching.R8PhaseEmbedding
