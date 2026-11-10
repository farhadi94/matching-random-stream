import RandomOrderMatching.Algebra.Tutte.LowerBound.Restriction
import RandomOrderMatching.Graph.EvenFactor.Basic

/-! Lower determinant degree for every actual bipartite directed factor,
even in a general ambient graph. Only crossing selected arcs are required;
noncrossing ambient variables are specialized away before fraction fields. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Algebra.Tutte.LowerBound
open RandomOrderMatching.Algebra.Tutte RandomOrderMatching.Graph.EvenFactor
set_option linter.unusedSectionVars false
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [LinearOrder V]

def crossEdge (L : Finset V) (e : Sym2 V) : Prop :=
  ∃ u v, u ∈ L ∧ v ∉ L ∧ e = s(u,v)

theorem crossEdge_pair (L : Finset V) (u v : V) :
    crossEdge L s(u,v) ↔ (u ∈ L ∧ v ∉ L) ∨ (u ∉ L ∧ v ∈ L) := by
  constructor
  · rintro ⟨x,y,hx,hy,he⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> tauto
  · rintro (⟨hu,hv⟩ | ⟨hu,hv⟩)
    · exact ⟨u,v,hu,hv,rfl⟩
    · exact ⟨v,u,hv,hu,Sym2.eq_swap⟩

def filteredGraph (G : SimpleGraph V) (p : Sym2 V → Prop) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ p s(u,v)
  symm := ⟨fun u v h => ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

/-- The selected matching arcs cross one cut; the ambient graph need not. -/
theorem tutte_selected_crossing_lower
    (G : SimpleGraph V) (w : Sym2 V → ℕ) (L : Finset V)
    (row col : ι → V) (hr : Function.Injective row) (hc : Function.Injective col)
    (hadj : ∀ i, G.Adj (row i) (col i))
    (hcross : ∀ i, (row i ∈ L ∧ col i ∉ L) ∨ (row i ∉ L ∧ col i ∈ L)) :
    ((weightedTutte G w).submatrix row col).det ≠ 0 ∧
    (∑ i, (w s(row i,col i) : ℤ)) ≤
      ((weightedTutte G w).submatrix row col).det.intDegree := by
  classical
  let H := filteredGraph G (crossEdge L)
  have hh : ∀ u v, H.Adj u v → (u ∈ L ∧ v ∉ L) ∨ (u ∉ L ∧ v ∈ L) := by
    intro u v ha
    exact (crossEdge_pair L u v).mp ha.2
  have ha : ∀ i, H.Adj (row i) (col i) := by
    intro i
    exact ⟨hadj i,(crossEdge_pair L _ _).mpr (hcross i)⟩
  obtain ⟨hn, hd⟩ := tutte_bipartite_partial_permutation_lower H w L hh row col hr hc ha
  obtain ⟨hGn, hGd⟩ := tutte_minor_restriction G H w (crossEdge L)
    (fun _ _ => Iff.rfl) row col hn
  exact ⟨hGn, hd.trans hGd⟩

/-- Ordinary-minor interface for the even-factor/Tutte interpretation. -/
theorem tutte_partial_factor_lower
    (G : SimpleGraph V) (w : Sym2 V → ℕ) (I : Finset V) (π : Equiv.Perm V)
    (hadj : ∀ i ∈ I, G.Adj i (π i))
    (hcolor : (arcSupport (I.image (fun v => (v,π v)))).Colorable 2) :
    ((weightedTutte G w).submatrix (fun i : {v // v ∈ I} => i.val)
      (fun i : {v // v ∈ I} => π i.val)).det ≠ 0 ∧
    (∑ i : {v // v ∈ I}, (w s(i.val,π i.val) : ℤ)) ≤
      ((weightedTutte G w).submatrix (fun i : {v // v ∈ I} => i.val)
        (fun i : {v // v ∈ I} => π i.val)).det.intDegree := by
  classical
  obtain ⟨c⟩ := hcolor
  let L := Finset.univ.filter (fun v => c v = 0)
  apply tutte_selected_crossing_lower G w L _ _ Subtype.val_injective
    (π.injective.comp Subtype.val_injective) (fun i => hadj i.val i.prop)
  intro i
  have hA : (arcSupport (I.image (fun v => (v,π v)))).Adj i.val (π i.val) := by
    refine ⟨G.ne_of_adj (hadj i.val i.prop), Or.inl ?_⟩
    exact Finset.mem_image.mpr ⟨i.val,i.prop,rfl⟩
  have hn := c.valid hA
  have h1 : c i.val = 0 ∨ c i.val = 1 := by omega
  have h2 : c (π i.val) = 0 ∨ c (π i.val) = 1 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp_all [L]

end RandomOrderMatching.Algebra.Tutte.LowerBound
#print axioms RandomOrderMatching.Algebra.Tutte.LowerBound.tutte_partial_factor_lower
