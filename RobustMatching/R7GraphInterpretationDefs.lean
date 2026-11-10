import RobustMatching.R7GraphDualBridge
import RobustMatching.R7GraphMarked
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! Shared, actual graph definitions for the generic Tutte interpretation.
An arc is directed from its matrix row to its matrix column. -/

noncomputable section
open scoped BigOperators symmDiff
open Classical

namespace RobustMatching.R7GraphInterpretation
open RobustMatching.R2Cut RobustMatching.R7GraphKonig

variable {V : Type*} [DecidableEq V]

def arcSupport (F : Finset (V × V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((u,v) ∈ F ∨ (v,u) ∈ F)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def sourceSupport (F : Finset (V × V)) : Finset V := F.image Prod.fst
def targetSupport (F : Finset (V × V)) : Finset V := F.image Prod.snd

/-- A loop-free partial permutation whose undirected support is bipartite.
For partial permutations this is precisely the even directed-factor condition. -/
structure EvenFactor (F : Finset (V × V)) : Prop where
  matching : RobustMatching.Dual.IsMatching F
  loopless : ∀ e ∈ F, e.1 ≠ e.2
  colorable : (arcSupport F).Colorable 2

def arcEdge (p : V × V) (hp : p.1 ≠ p.2) : Edge V :=
  ⟨{p.1,p.2},by simp [hp]⟩

def arcWeight (w : Edge V → ℝ) (p : V × V) : ℝ :=
  if hp : p.1 ≠ p.2 then w (arcEdge p hp) else 0

theorem arcWeight_eq (w : Edge V → ℝ) (p : V × V) (hp : p.1 ≠ p.2) :
    arcWeight w p = w (arcEdge p hp) := by simp [arcWeight,hp]

def looplessArcs (F : Finset (V × V)) : Finset {p : V × V // p.1 ≠ p.2} :=
  (F.filter fun p => p.1 ≠ p.2).attach.image fun p =>
    ⟨p.val,by simpa only [Finset.mem_filter] using (Finset.mem_filter.mp p.property).2⟩

def arcGraph (F : Finset (V × V)) : Graph V :=
  (looplessArcs F).image fun p => arcEdge p.val p.property

theorem mem_looplessArcs {F : Finset (V × V)} {p : V × V} (hp : p.1 ≠ p.2) :
    (⟨p,hp⟩ : {p : V × V // p.1 ≠ p.2}) ∈ looplessArcs F ↔ p ∈ F := by
  simp only [looplessArcs,Finset.mem_image,Finset.mem_attach,true_and,Subtype.mk.injEq]
  constructor
  · rintro ⟨q,hq⟩
    have he := (Finset.mem_filter.mp q.property).1
    simpa [hq] using he
  · intro he
    exact ⟨⟨p,Finset.mem_filter.mpr ⟨he,hp⟩⟩,rfl⟩

theorem mem_arcGraph {F : Finset (V × V)} {e : Edge V} :
    e ∈ arcGraph F ↔ ∃ p ∈ F, ∃ hp : p.1 ≠ p.2, arcEdge p hp = e := by
  constructor
  · intro he
    obtain ⟨p,hp,hpe⟩ := Finset.mem_image.mp he
    exact ⟨p.val,(mem_looplessArcs p.property).mp hp,p.property,hpe⟩
  · rintro ⟨p,hp,hne,rfl⟩
    exact Finset.mem_image.mpr ⟨⟨p,hne⟩,(mem_looplessArcs hne).mpr hp,rfl⟩

theorem arcGraph_simpleGraph (F : Finset (V × V)) :
    simpleGraph (arcGraph F) = arcSupport F := by
  ext u v
  constructor
  · rintro ⟨⟨e,he,heq⟩,hne⟩
    obtain ⟨p,hp,hpne,rfl⟩ := mem_arcGraph.mp he
    have heq' : ({u,v} : Finset V) = {p.1,p.2} := by
      simpa [arcEdge,Sym2.toFinset_mk_eq] using heq
    have hu : u = p.1 ∨ u = p.2 := by
      have hh : u ∈ ({p.1,p.2} : Finset V) := heq' ▸ (by simp)
      simpa using hh
    have hv : v = p.1 ∨ v = p.2 := by
      have hh : v ∈ ({p.1,p.2} : Finset V) := heq' ▸ (by simp)
      simpa using hh
    refine ⟨hne,?_⟩
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact (hne (hu.trans hv.symm)).elim
    · exact Or.inl (by simpa [hu,hv] using hp)
    · exact Or.inr (by simpa [hu,hv] using hp)
    · exact (hne (hu.trans hv.symm)).elim
  · rintro ⟨hne,hor⟩
    refine ⟨?_,hne⟩
    rcases hor with h | h
    · exact ⟨arcEdge (u,v) hne,mem_arcGraph.mpr ⟨(u,v),h,hne,rfl⟩,
        by simp [arcEdge,Sym2.toFinset_mk_eq]⟩
    · exact ⟨arcEdge (v,u) hne.symm,
        mem_arcGraph.mpr ⟨(v,u),h,hne.symm,rfl⟩,
        by simp [arcEdge,Sym2.toFinset_mk_eq,Finset.pair_comm]⟩

end RobustMatching.R7GraphInterpretation
