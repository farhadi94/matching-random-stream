import RandomOrderMatching.Analysis.FixedHost.Coordinates
import RandomOrderMatching.Phases.Embedding.ParentMaps

/-! Physical suffix labels for the actual copied benchmark. They are
selected from actual parent identities, with no multiplicity hypothesis. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
namespace RandomOrderMatching.Analysis.FixedHost
open RandomOrderMatching.Graph RandomOrderMatching.Analysis.Profile RandomOrderMatching.Phases.Embedding
variable {V B : Type*} [Fintype V] [LinearOrder V]

def physicalParents {W : ℕ} (MC : Graph (V×Fin W)) (original : B→Edge V)
    (parent : Edge (V×Fin W)→Edge V)
    (hlabels : ∀f∈MC,∃b,original b=parent f) : MC→B :=
  fun f=>Classical.choose (hlabels f.val f.property)

theorem physicalParents_identity {W : ℕ} (MC : Graph (V×Fin W)) (original : B→Edge V)
    (parent : Edge (V×Fin W)→Edge V) (hlabels : ∀f∈MC,∃b,original b=parent f)
    (f : MC) : parent f.val=original (physicalParents MC original parent hlabels f) :=
  (Classical.choose_spec (hlabels f.val f.property)).symm

theorem consistent_parent_endpoint {W : ℕ} (MC : Graph (V×Fin W))
    (original : B→Edge V) (parent : Edge (V×Fin W)→Edge V) (w : Edge V→ℕ)
    (hcopies : ConsistentCopies W w parent MC) (par : MC→B)
    (hpar : ∀f:MC,parent f.val=original (par f)) (f : MC) :
    ∃i:Fin W,(endpoint (original (par f)) 0,i)∈f.val.val := by
  have he : endpoint (original (par f)) 0∈f.val.val.image Prod.fst := by
    rw [hcopies.projection f.val f.property,hpar f]
    exact endpoint_mem _ _
  obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp he
  exact ⟨x.2,by simpa only [←hxe] using hx⟩

theorem physicalParents_fiber_le {W : ℕ} (MC : Graph (V×Fin W)) (hm : Matching MC)
    (original : B→Edge V) (parent : Edge (V×Fin W)→Edge V) (w : Edge V→ℕ)
    (hcopies : ConsistentCopies W w parent MC)
    (hlabels : ∀f∈MC,∃b,original b=parent f) (b : B) :
    Fintype.card {f:MC //physicalParents MC original parent hlabels f=b}≤W :=
  parent_fiber_le MC hm (physicalParents MC original parent hlabels)
    (fun b=>endpoint (original b) 0)
    (consistent_parent_endpoint MC original parent w hcopies
      (physicalParents MC original parent hlabels) (physicalParents_identity MC original parent hlabels)) b

end RandomOrderMatching.Analysis.FixedHost
