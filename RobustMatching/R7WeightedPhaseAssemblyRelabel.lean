import RobustMatching.R7GraphDualBridge
import RobustMatching.R7AlgebraPathValue

/-! Injective vertex relabeling of actual finite edge graphs. These lemmas
transport typed repair matchings to canonical original/copy vertices,
without assuming that graph ranks are preserved. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7WeightedPhaseAssembly
open RobustMatching.R2Cut RobustMatching.R7AlgebraPath
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def mapEdge (f : V → W) (hf : Function.Injective f) (e : Edge V) : Edge W :=
  ⟨e.val.image f, by rw [Finset.card_image_of_injective _ hf,e.property]⟩

def mapGraph (f : V → W) (hf : Function.Injective f) (G : Graph V) : Graph W :=
  G.image (mapEdge f hf)

theorem mapEdge_injective (f : V → W) (hf : Function.Injective f) :
    Function.Injective (mapEdge f hf) := by
  intro e g he
  have hv := congrArg Subtype.val he
  change e.val.image f = g.val.image f at hv
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    have hh : f x ∈ g.val.image f := hv ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hh
    exact hf heq ▸ hy
  · intro hx
    have hh : f x ∈ e.val.image f := hv.symm ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hh
    exact hf heq ▸ hy

theorem mapGraph_mono (f : V → W) (hf : Function.Injective f)
    {G K : Graph V} (h : G ⊆ K) : mapGraph f hf G ⊆ mapGraph f hf K :=
  Finset.image_subset_image h

theorem mapGraph_card (f : V → W) (hf : Function.Injective f) (G : Graph V) :
    (mapGraph f hf G).card = G.card :=
  Finset.card_image_of_injective _ (mapEdge_injective f hf)

theorem mapGraph_matching_iff (f : V → W) (hf : Function.Injective f) (G : Graph V) :
    Matching (mapGraph f hf G) ↔ Matching G := by
  constructor
  · intro hm e he g hg hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hn : mapEdge f hf e ≠ mapEdge f hf g := fun h => hne (mapEdge_injective f hf h)
    have hd := hm (Finset.mem_image_of_mem _ he) (Finset.mem_image_of_mem _ hg) hn
    exact Finset.disjoint_left.mp hd (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      (Finset.mem_image.mpr ⟨x,hy,rfl⟩)
  · intro hm e he g hg hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hg
    have hn : a ≠ b := fun h => hne (congrArg (mapEdge f hf) h)
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨x',hx',hx'y⟩ := Finset.mem_image.mp hy'
    have heq : x = x' := hf (hxy.trans hx'y.symm)
    exact Finset.disjoint_left.mp (hm ha hb hn) hx (heq.symm ▸ hx')

theorem mapGraph_subgraph_pullback (f : V → W) (hf : Function.Injective f)
    (G : Graph V) (K : Graph W) (hK : K ⊆ mapGraph f hf G) :
    ∃ A ⊆ G, mapGraph f hf A = K := by
  let A := G.filter (fun e => mapEdge f hf e ∈ K)
  refine ⟨A,Finset.filter_subset _ _,?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp ha).2
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (hK he)
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,he⟩,rfl⟩

theorem mapGraph_rank (f : V → W) (hf : Function.Injective f) (G : Graph V) :
    rank (mapGraph f hf G) = rank G := by
  apply le_antisymm
  · obtain ⟨K,hK,hm,hcard⟩ := rank_attained (mapGraph f hf G)
    obtain ⟨A,hA,hAK⟩ := mapGraph_subgraph_pullback f hf G K hK
    have ha : Matching A := (mapGraph_matching_iff f hf A).mp (hAK.symm ▸ hm)
    have hh := matching_card_le_rank hA ha
    rw [←hcard,←hAK,mapGraph_card]
    exact hh
  · obtain ⟨A,hA,hm,hcard⟩ := rank_attained G
    have hh := matching_card_le_rank (mapGraph_mono f hf hA)
      ((mapGraph_matching_iff f hf A).mpr hm)
    rw [mapGraph_card,hcard] at hh
    exact hh

theorem mapEdge_disjoint_image_iff (f : V → W) (hf : Function.Injective f)
    (e : Edge V) (S : Finset V) :
    Disjoint (mapEdge f hf e).val (S.image f) ↔ Disjoint e.val S := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro x hx hs
    exact Finset.disjoint_left.mp h (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      (Finset.mem_image.mpr ⟨x,hs,rfl⟩)
  · intro h
    apply Finset.disjoint_left.mpr
    intro y hy hs
    obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp hs
    have heq := hf (hxy.trans hzy.symm)
    exact Finset.disjoint_left.mp h hx (heq.symm ▸ hz)

theorem mapGraph_delete (f : V → W) (hf : Function.Injective f)
    (G : Graph V) (S : Finset V) :
    mapGraph f hf (deleteVertices G S) = deleteVertices (mapGraph f hf G) (S.image f) := by
  ext e
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨ha,hd⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ha,
      (mapEdge_disjoint_image_iff f hf a S).mpr hd⟩
  · intro he
    obtain ⟨he,hd⟩ := Finset.mem_filter.mp he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr
      ⟨ha,(mapEdge_disjoint_image_iff f hf a S).mp hd⟩,rfl⟩

/-- Extract a native endpoint-pair matching of exactly the source graph's
rank after an injective copied-vertex embedding into a bipartite support. -/
theorem rank_matching_into_pairs {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (f : V → L ⊕ R) (hf : Function.Injective f) (G : Graph V)
    (E : Finset (L × R)) (hG : mapGraph f hf G ⊆ RobustMatching.R7GraphDualBridge.encode E) :
    ∃ M ⊆ E, RobustMatching.Dual.IsMatching M ∧ M.card = rank G := by
  obtain ⟨A,hA,hm,hcard⟩ := rank_attained G
  have hh := (mapGraph_mono f hf hA).trans hG
  obtain ⟨M,hM,hmap,hmatch⟩ := RobustMatching.R7GraphDualBridge.decode_subgraph hh
  refine ⟨M,hM,hmatch.mp ((mapGraph_matching_iff f hf A).mpr hm),?_⟩
  have hc := congrArg Finset.card hmap
  rw [RobustMatching.R7GraphDualBridge.encode_card,mapGraph_card,hcard] at hc
  exact hc

/-- Decode an entire actual matching through an injective vertex map. -/
theorem matching_into_pairs {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (f : V → L ⊕ R) (hf : Function.Injective f) (G : Graph V) (hm : Matching G)
    (E : Finset (L × R)) (hG : mapGraph f hf G ⊆ RobustMatching.R7GraphDualBridge.encode E) :
    ∃ M ⊆ E, RobustMatching.Dual.IsMatching M ∧ M.card = G.card ∧
      RobustMatching.R7GraphDualBridge.encode M = mapGraph f hf G := by
  obtain ⟨M,hM,hmap,hmatch⟩ := RobustMatching.R7GraphDualBridge.decode_subgraph hG
  refine ⟨M,hM,hmatch.mp ((mapGraph_matching_iff f hf G).mpr hm),?_,hmap⟩
  have hc := congrArg Finset.card hmap
  rwa [RobustMatching.R7GraphDualBridge.encode_card,mapGraph_card] at hc

theorem mapGraph_covered (f : V → W) (hf : Function.Injective f) (G : Graph V) :
    covered (mapGraph f hf G) = (covered G).image f := by
  ext y
  constructor
  · intro hy
    obtain ⟨e,he,hye⟩ := mem_covered.mp hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hye
    exact Finset.mem_image.mpr ⟨x,mem_covered.mpr ⟨a,ha,hx⟩,rfl⟩
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨a,ha,hxa⟩ := mem_covered.mp hx
    exact mem_covered.mpr ⟨mapEdge f hf a,Finset.mem_image_of_mem _ ha,
      Finset.mem_image.mpr ⟨x,hxa,rfl⟩⟩

end RobustMatching.R7WeightedPhaseAssembly
#print axioms RobustMatching.R7WeightedPhaseAssembly.mapGraph_rank
#print axioms RobustMatching.R7WeightedPhaseAssembly.rank_matching_into_pairs
