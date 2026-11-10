import RobustMatching.R7GraphMatrix
import RobustMatching.R1DualLattice

/-! Exact conversions between the endpoint-injective bipartite matching API
and the project's two-vertex-edge graph matching API. -/

noncomputable section
open scoped BigOperators
open Classical

namespace RobustMatching.R7GraphDualBridge
open RobustMatching.R2Cut RobustMatching.R7GraphMatrix

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def encode (M : Finset (L × R)) : Graph (L ⊕ R) := M.image edgeOf

theorem encode_matching_iff (M : Finset (L × R)) :
    Matching (encode M) ↔ RobustMatching.Dual.IsMatching M := by
  constructor
  · intro hm
    constructor
    · intro a ha b hb heq
      by_contra hn
      have hne : edgeOf a ≠ edgeOf b := fun hh => hn (edgeOf_injective hh)
      have hd := hm (Finset.mem_image_of_mem edgeOf ha) (Finset.mem_image_of_mem edgeOf hb) hne
      exact Finset.disjoint_left.mp hd (show Sum.inl a.1 ∈ (edgeOf a).val by simp [edgeOf])
        (by simp [edgeOf,heq])
    · intro a ha b hb heq
      by_contra hn
      have hne : edgeOf a ≠ edgeOf b := fun hh => hn (edgeOf_injective hh)
      have hd := hm (Finset.mem_image_of_mem edgeOf ha) (Finset.mem_image_of_mem edgeOf hb) hne
      exact Finset.disjoint_left.mp hd (show Sum.inr a.2 ∈ (edgeOf a).val by simp [edgeOf])
        (by simp [edgeOf,heq])
  · intro hm e he f hf hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hf
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    simp only [edgeOf,Finset.mem_insert,Finset.mem_singleton] at hva hvb
    rcases hva with rfl | rfl <;> rcases hvb with heq | heq
    · exact hne (congrArg edgeOf (hm.1 ha hb (Sum.inl.inj heq)))
    · cases heq
    · cases heq
    · exact hne (congrArg edgeOf (hm.2 ha hb (Sum.inr.inj heq)))

theorem encode_card (M : Finset (L × R)) : (encode M).card = M.card :=
  Finset.card_image_of_injective _ edgeOf_injective

theorem encode_sum (M : Finset (L × R)) (w : Edge (L ⊕ R) → ℝ) :
    (∑ e ∈ encode M, w e) = ∑ p ∈ M, w (edgeOf p) :=
  Finset.sum_image edgeOf_injective.injOn

theorem encode_covered (M : Finset (L × R)) :
    covered (encode M) = (M.image fun p => Sum.inl p.1) ∪ (M.image fun p => Sum.inr p.2) := by
  ext v
  simp only [mem_covered,encode,Finset.mem_image,Finset.mem_union]
  constructor
  · rintro ⟨e,⟨p,hp,rfl⟩,hv⟩
    simp only [edgeOf,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · exact Or.inl ⟨p,hp,hv.symm⟩
    · exact Or.inr ⟨p,hp,hv.symm⟩
  · rintro (⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
    · exact ⟨edgeOf p,⟨p,hp,rfl⟩,by simp [edgeOf]⟩
    · exact ⟨edgeOf p,⟨p,hp,rfl⟩,by simp [edgeOf]⟩

theorem decode_subgraph {E : Finset (L × R)} {K : Graph (L ⊕ R)}
    (hK : K ⊆ encode E) :
    ∃ M ⊆ E, encode M = K ∧ (Matching K ↔ RobustMatching.Dual.IsMatching M) := by
  let M := E.filter fun p => edgeOf p ∈ K
  have heq : encode M = K := by
    ext e
    constructor
    · intro he
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hp).2
    · intro he
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hK he)
      exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,he⟩,rfl⟩
  exact ⟨M,Finset.filter_subset _ _,heq,heq ▸ encode_matching_iff M⟩

end RobustMatching.R7GraphDualBridge

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphDualBridge.encode_matching_iff
#print axioms RobustMatching.R7GraphDualBridge.decode_subgraph
