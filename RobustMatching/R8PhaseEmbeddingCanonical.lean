import RobustMatching.R8PhaseEmbeddingRecords
import RobustMatching.R8AcquisitionCanonicalGraph

/-! Discharge copied-parent/index premises from the actual canonical batches. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
namespace RobustMatching.R8PhaseEmbedding
open R2Cut R8Acquisition R7GraphBipartiteExchange
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem edge_pair_of_mem {X : Type*} [DecidableEq X] (e : Edge X)
    {x y : X} (hx : x∈e.val) (hy : y∈e.val) (hne : x≠y) : e.val={x,y} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl <;> assumption
  · simp [e.property,hne]

theorem canonical_copies_consistent (W : ℕ) (w : Edge V→ℕ) (hw : ∀e,w e≤W)
    (fallback : Edge V) (labels : List (Edge V)) :
    ConsistentCopies W w (canonicalParent W fallback) (seenCopies (canonicalCopies W w hw) labels) := by
  constructor
  · intro f hf
    obtain ⟨e,_,hf⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hf)
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    rw [canonicalParent_copy,canonicalCopy_projection]
  · intro f hf x hx y hy hne
    obtain ⟨e,_,hf⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hf)
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    rw [canonicalParent_copy]
    exact (canonicalCopy_pair_data W w hw e i x y hne
      (edge_pair_of_mem _ hx hy hne)).2

/-- Restriction or any other partial support of actually emitted canonical
copies inherits both exact original-parent and antidiagonal laws. -/
theorem canonical_partial_consistent (W : ℕ) (w : Edge V→ℕ) (hw : ∀e,w e≤W)
    (fallback : Edge V) (labels : List (Edge V)) (A : Graph (V×Fin W))
    (hA : A⊆seenCopies (canonicalCopies W w hw) labels) :
    ConsistentCopies W w (canonicalParent W fallback) A :=
  (canonical_copies_consistent W w hw fallback labels).mono hA

/-- A parent's fixed original endpoint is present in every one of its
canonical copies, yielding the elementary probability fiber interface. -/
theorem canonical_parent_endpoint (W : ℕ) (w : Edge V→ℕ) (hw : ∀e,w e≤W)
    (fallback : Edge V) (labels : List (Edge V)) {f : Edge (V×Fin W)}
    (hf : f∈seenCopies (canonicalCopies W w hw) labels) :
    ∃i:Fin W,(R7SupportFlowMap.endpoint (canonicalParent W fallback f) 0,i)∈f.val := by
  obtain ⟨e,_,hf⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hf)
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  rw [canonicalParent_copy]
  exact ⟨⟨i.val,lt_of_lt_of_le i.isLt (hw e)⟩,by simp [canonicalCopy]⟩

end RobustMatching.R8PhaseEmbedding
