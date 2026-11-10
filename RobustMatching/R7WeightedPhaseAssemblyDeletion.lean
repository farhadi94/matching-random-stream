import RobustMatching.R7WeightedPhaseAssemblyRelabel

/-! Injective vertex labels preserve the actual selected endpoint
 deletions on the analytic cut. The cover/outside partition is unrelated
 to this cut and is never used as the bipartition. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7WeightedPhaseAssembly
open RobustMatching.R2Cut RobustMatching.R7AlgebraPath
variable {T L R : Type*} [DecidableEq T] [DecidableEq L] [DecidableEq R]
variable [Fintype L] [Fintype R]

def copySide : L ⊕ R → Bool := Sum.elim (fun _ => false) (fun _ => true)

theorem mapped_selected_left
    (f : T → L ⊕ R) (hf : Function.Injective f) (J : Graph T)
    (S : Finset (L × R)) (hJ : mapGraph f hf J = R7GraphDualBridge.encode S)
    (side : T → Bool) (hside : ∀ v, copySide (f v) = side v) :
    ((covered J).filter (fun v => side v = false)).image f =
      S.image (fun p => Sum.inl p.1) := by
  classical
  have hc := mapGraph_covered f hf J
  rw [hJ,R7GraphDualBridge.encode_covered] at hc
  ext y
  constructor
  · intro hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hv,hs⟩ := Finset.mem_filter.mp hv
    have hm : f v ∈ (S.image (fun p => Sum.inl p.1)) ∪
        (S.image (fun p => Sum.inr p.2)) := hc.symm ▸ Finset.mem_image_of_mem f hv
    rcases Finset.mem_union.mp hm with hl | hr
    · exact hl
    · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hr
      have hh := hside v
      rw [←he] at hh
      simp [copySide,hs] at hh
  · intro hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
    have hm : Sum.inl p.1 ∈ (covered J).image f := hc ▸
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hm
    refine Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,?_⟩,he⟩
    have hh := hside v
    rw [he] at hh
    exact hh.symm

theorem mapped_selected_right
    (f : T → L ⊕ R) (hf : Function.Injective f) (J : Graph T)
    (S : Finset (L × R)) (hJ : mapGraph f hf J = R7GraphDualBridge.encode S)
    (side : T → Bool) (hside : ∀ v, copySide (f v) = side v) :
    ((covered J).filter (fun v => side v = true)).image f =
      S.image (fun p => Sum.inr p.2) := by
  classical
  have hc := mapGraph_covered f hf J
  rw [hJ,R7GraphDualBridge.encode_covered] at hc
  ext y
  constructor
  · intro hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hv,hs⟩ := Finset.mem_filter.mp hv
    have hm : f v ∈ (S.image (fun p => Sum.inl p.1)) ∪
        (S.image (fun p => Sum.inr p.2)) := hc.symm ▸ Finset.mem_image_of_mem f hv
    rcases Finset.mem_union.mp hm with hl | hr
    · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hl
      have hh := hside v
      rw [←he] at hh
      simp [copySide,hs] at hh
    · exact hr
  · intro hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
    have hm : Sum.inr p.2 ∈ (covered J).image f := hc ▸
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hm
    refine Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,?_⟩,he⟩
    have hh := hside v
    rw [he] at hh
    exact hh.symm

theorem delete_encode_left (B S : Finset (L × R)) :
    deleteVertices (R7GraphDualBridge.encode B) (S.image (fun p => Sum.inl p.1)) =
      R7GraphDualBridge.encode (B.filter (fun p => p.1 ∉ S.image Prod.fst)) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨he,hd⟩ := Finset.mem_filter.mp he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_image.mpr
    refine ⟨p,Finset.mem_filter.mpr ⟨hp,?_⟩,rfl⟩
    intro hh
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hh
    exact Finset.disjoint_left.mp hd (show Sum.inl p.1 ∈ (R7GraphMatrix.edgeOf p).val by
      simp [R7GraphMatrix.edgeOf]) (Finset.mem_image.mpr ⟨q,hq,congrArg Sum.inl heq⟩)
  · intro he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hp,?_⟩
    apply Finset.disjoint_left.mpr
    intro v hv hs
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    simp only [R7GraphMatrix.edgeOf,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hh | hh
    · exact hn (Finset.mem_image.mpr ⟨q,hq,Sum.inl.inj hh⟩)
    · cases hh

theorem delete_encode_right (B S : Finset (L × R)) :
    deleteVertices (R7GraphDualBridge.encode B) (S.image (fun p => Sum.inr p.2)) =
      R7GraphDualBridge.encode (B.filter (fun p => p.2 ∉ S.image Prod.snd)) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨he,hd⟩ := Finset.mem_filter.mp he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_image.mpr
    refine ⟨p,Finset.mem_filter.mpr ⟨hp,?_⟩,rfl⟩
    intro hh
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hh
    exact Finset.disjoint_left.mp hd (show Sum.inr p.2 ∈ (R7GraphMatrix.edgeOf p).val by
      simp [R7GraphMatrix.edgeOf]) (Finset.mem_image.mpr ⟨q,hq,congrArg Sum.inr heq⟩)
  · intro he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hp,?_⟩
    apply Finset.disjoint_left.mpr
    intro v hv hs
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    simp only [R7GraphMatrix.edgeOf,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hh | hh
    · cases hh
    · exact hn (Finset.mem_image.mpr ⟨q,hq,Sum.inr.inj hh⟩)

theorem relabelled_deletion_left
    (f : T → L ⊕ R) (hf : Function.Injective f) (A J : Graph T)
    (B S : Finset (L × R)) (hA : mapGraph f hf A ⊆ R7GraphDualBridge.encode B)
    (hJ : mapGraph f hf J = R7GraphDualBridge.encode S)
    (side : T → Bool) (hside : ∀ v, copySide (f v) = side v) :
    mapGraph f hf (deleteVertices A ((covered J).filter (fun v => side v = false))) ⊆
      R7GraphDualBridge.encode (B.filter (fun p => p.1 ∉ S.image Prod.fst)) := by
  rw [mapGraph_delete,mapped_selected_left f hf J S hJ side hside,←delete_encode_left]
  intro e he
  obtain ⟨he,hd⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hA he,hd⟩

theorem relabelled_deletion_right
    (f : T → L ⊕ R) (hf : Function.Injective f) (A J : Graph T)
    (B S : Finset (L × R)) (hA : mapGraph f hf A ⊆ R7GraphDualBridge.encode B)
    (hJ : mapGraph f hf J = R7GraphDualBridge.encode S)
    (side : T → Bool) (hside : ∀ v, copySide (f v) = side v) :
    mapGraph f hf (deleteVertices A ((covered J).filter (fun v => side v = true))) ⊆
      R7GraphDualBridge.encode (B.filter (fun p => p.2 ∉ S.image Prod.snd)) := by
  rw [mapGraph_delete,mapped_selected_right f hf J S hJ side hside,←delete_encode_right]
  intro e he
  obtain ⟨he,hd⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hA he,hd⟩

end RobustMatching.R7WeightedPhaseAssembly
#print axioms RobustMatching.R7WeightedPhaseAssembly.relabelled_deletion_left
#print axioms RobustMatching.R7WeightedPhaseAssembly.relabelled_deletion_right
