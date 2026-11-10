import RobustMatching.R7WeightedPhaseAssemblyEmbedding
import RobustMatching.R7GraphInterpretationFactor

/-! Canonical original-cut coordinates for actual copied vertices. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RobustMatching.R8PhaseEmbedding
open R2Cut R7WeightedPhaseAssembly R7CopyDualGeneralBridge
open R7GraphBipartiteExchange
variable {V : Type*} [Fintype V] [LinearOrder V]

def copyCut (C : Finset V) (W : ℕ) : Finset (V×Fin W) :=
  Finset.univ.filter fun x => x.1∈C

def copyLabel (C : Finset V) (W : ℕ) :
    (V×Fin W) ≃ (Left C×Fin W)⊕(Right C×Fin W) where
  toFun x := if h:x.1∈C then .inl (⟨x.1,h⟩,x.2) else .inr (⟨x.1,h⟩,x.2)
  invFun := Sum.elim (fun x => (x.1.val,x.2)) (fun x => (x.1.val,x.2))
  left_inv := by intro x; dsimp; split <;> rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨v,hv⟩,i⟩ | ⟨⟨v,hv⟩,i⟩ <;> simp [hv]

def originalSide (C : Finset V) (v : V) : Bool := if v∈C then false else true

theorem copyLabel_side (C : Finset V) (W : ℕ) (x : V×Fin W) :
    copySide (copyLabel C W x)=originalSide C x.1 := by
  simp only [copyLabel,Equiv.coe_fn_mk,originalSide]
  split <;> rfl

theorem originalSide_false_cut (z : V→Bool) (v : V) :
    originalSide (Finset.univ.filter fun u=>z u=false) v=z v := by
  cases hz:z v <;> simp [originalSide,hz]

section Relabel
variable {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

theorem mapEdge_comp (f : X→Y) (hf : Function.Injective f)
    (g : Y→Z) (hg : Function.Injective g) (e : Edge X) :
    mapEdge g hg (mapEdge f hf e)=mapEdge (g∘f) (hg.comp hf) e := by
  apply Subtype.ext
  exact Finset.image_image

theorem mapGraph_comp (f : X→Y) (hf : Function.Injective f)
    (g : Y→Z) (hg : Function.Injective g) (A : Graph X) :
    mapGraph g hg (mapGraph f hf A)=mapGraph (g∘f) (hg.comp hf) A := by
  simp only [mapGraph,Finset.image_image,Function.comp_def,mapEdge_comp]

theorem mapEdge_equiv_symm (f : X≃Y) (e : Edge X) :
    mapEdge f.symm f.symm.injective (mapEdge f f.injective e)=e := by
  apply Subtype.ext
  simp only [mapEdge,Finset.image_image]
  simpa using Finset.image_id e.val

theorem mapGraph_equiv_symm (f : X≃Y) (A : Graph X) :
    mapGraph f.symm f.symm.injective (mapGraph f f.injective A)=A := by
  simp only [mapGraph,Finset.image_image,Function.comp_def,mapEdge_equiv_symm]
  change Finset.image id A=A
  exact Finset.image_id
end Relabel

abbrev CopyPair (C : Finset V) (W : ℕ) := (Left C×Fin W)×(Right C×Fin W)

def physicalEdge (C : Finset V) (W : ℕ) (p : CopyPair C W) : Edge (V×Fin W) :=
  mapEdge (copyLabel C W).symm (copyLabel C W).symm.injective (R7GraphMatrix.edgeOf p)

theorem physicalEdge_val (C : Finset V) (W : ℕ) (p : CopyPair C W) :
    (physicalEdge C W p).val = {(p.1.1.val,p.1.2),(p.2.1.val,p.2.2)} := by
  simp [physicalEdge,mapEdge,R7GraphMatrix.edgeOf,copyLabel]

theorem physicalEdge_injective (C : Finset V) (W : ℕ) :
    Function.Injective (physicalEdge C W) :=
  (mapEdge_injective _ (copyLabel C W).symm.injective).comp R7GraphMatrix.edgeOf_injective

theorem physicalEdge_label (C : Finset V) (W : ℕ) (p : CopyPair C W) :
    mapEdge (copyLabel C W) (copyLabel C W).injective (physicalEdge C W p)=
      R7GraphMatrix.edgeOf p := by
  exact mapEdge_equiv_symm (copyLabel C W).symm _

def copiedPairs (C : Finset V) (W : ℕ) (A : Graph (V×Fin W)) : Finset (CopyPair C W) :=
  Finset.univ.filter fun p => physicalEdge C W p ∈ A

theorem mem_copiedPairs (C : Finset V) (W : ℕ) (A : Graph (V×Fin W)) (p : CopyPair C W) :
    p∈copiedPairs C W A ↔ physicalEdge C W p∈A := by simp [copiedPairs]

theorem crossing_edge_pair (C : Finset V) (W : ℕ) {A : Graph (V×Fin W)}
    (hA : Crosses A (copyCut C W)) {e : Edge (V×Fin W)} (he : e∈A) :
    ∃ p : CopyPair C W, physicalEdge C W p=e := by
  obtain ⟨u,v,hn,hev⟩ := Finset.card_eq_two.mp e.property
  have hu : u∈e.val := by rw [hev]; simp
  have hv : v∈e.val := by rw [hev]; simp
  have hs := R7GraphInterpretation.crossing_edge_sides hA he hu hv hn
  simp only [copyCut,Finset.mem_filter,Finset.mem_univ,true_and] at hs
  by_cases huc:u.1∈C
  · have hvc : v.1∉C := hs.mp huc
    refine ⟨((⟨u.1,huc⟩,u.2),(⟨v.1,hvc⟩,v.2)),?_⟩
    apply Subtype.ext
    rw [physicalEdge_val,hev]
  · have hvc : v.1∈C := not_not.mp (fun h=>huc (hs.mpr h))
    refine ⟨((⟨v.1,hvc⟩,v.2),(⟨u.1,huc⟩,u.2)),?_⟩
    apply Subtype.ext
    rw [physicalEdge_val,hev]
    exact Finset.pair_comm _ _

theorem copiedPairs_encode (C : Finset V) (W : ℕ) (A : Graph (V×Fin W))
    (hA : Crosses A (copyCut C W)) :
    mapGraph (copyLabel C W) (copyLabel C W).injective A=
      R7GraphDualBridge.encode (copiedPairs C W A) := by
  classical
  unfold mapGraph R7GraphDualBridge.encode
  ext e
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨f,hf,rfl⟩
    obtain ⟨p,hp⟩ := crossing_edge_pair C W hA hf
    rw [←hp,physicalEdge_label]
    exact ⟨p,(mem_copiedPairs C W A p).mpr (hp.symm ▸ hf),rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨physicalEdge C W p,(mem_copiedPairs C W A p).mp hp,
      physicalEdge_label C W p⟩

end RobustMatching.R8PhaseEmbedding
