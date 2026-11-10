import RobustMatching.R7SupportFlowMap

/-! Every actual benchmark matching admits the canonical endpoint coordinates
used by the typed map. This is a vertex bijection respecting each individual
edge, not merely an equality of total cardinalities. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R2Cut

variable {V : Type*} [Fintype V] [DecidableEq V]

def endpointEquiv (e : Edge V) : Fin 2 ≃ {v : V // v ∈ e.val} :=
  (Fintype.equivFinOfCardEq (show Fintype.card {v : V // v ∈ e.val}=2 by
    simpa using e.property)).symm

def endpoint (e : Edge V) (i : Fin 2) : V := (endpointEquiv e i).val

theorem endpoint_mem (e : Edge V) (i : Fin 2) : endpoint e i ∈ e.val :=
  (endpointEquiv e i).property

theorem endpoint_injective (e : Edge V) : Function.Injective (endpoint e) := by
  intro i j hij
  exact (endpointEquiv e).injective (Subtype.ext hij)

theorem endpoint_surjective (e : Edge V) (v : V) (hv : v ∈ e.val) :
    ∃ i, endpoint e i=v := by
  refine ⟨(endpointEquiv e).symm ⟨v,hv⟩,?_⟩
  simp [endpoint]

abbrev MatchingVertex (M : Graph V) := (M × Fin 2) ⊕ {v : V // v ∉ covered M}

def matchingCoordinateMap (M : Graph V) : MatchingVertex M → V
  | .inl (e,i) => endpoint e.val i
  | .inr v => v.val

theorem matchingCoordinateMap_injective (M : Graph V) (hM : Matching M) :
    Function.Injective (matchingCoordinateMap M) := by
  intro x y hxy
  cases x with
  | inl x =>
    rcases x with ⟨e,i⟩
    cases y with
    | inl y =>
      rcases y with ⟨f,j⟩
      have hef : e=f := by
        apply Subtype.ext
        by_contra hne
        have hd := hM e.property f.property hne
        have hs : endpoint e.val i=endpoint f.val j := hxy
        exact Finset.disjoint_left.mp hd (endpoint_mem e.val i)
          (hs.symm ▸ endpoint_mem f.val j)
      subst f
      have hij : i=j := endpoint_injective e.val hxy
      subst j
      rfl
    | inr v =>
      have hc : endpoint e.val i ∈ covered M :=
        mem_covered.mpr ⟨e.val,e.property,endpoint_mem e.val i⟩
      have hs : endpoint e.val i=v.val := hxy
      exact (v.property (hs ▸ hc)).elim
  | inr v =>
    cases y with
    | inl y =>
      rcases y with ⟨e,i⟩
      have hc : endpoint e.val i ∈ covered M :=
        mem_covered.mpr ⟨e.val,e.property,endpoint_mem e.val i⟩
      have hs : v.val=endpoint e.val i := hxy
      exact (v.property (hs.symm ▸ hc)).elim
    | inr w =>
      exact congrArg Sum.inr (Subtype.ext hxy)

theorem matchingCoordinateMap_surjective (M : Graph V) :
    Function.Surjective (matchingCoordinateMap M) := by
  intro v
  by_cases hv : v ∈ covered M
  · obtain ⟨e,he,hve⟩ := mem_covered.mp hv
    obtain ⟨i,hi⟩ := endpoint_surjective e v hve
    exact ⟨.inl (⟨e,he⟩,i),hi⟩
  · exact ⟨.inr ⟨v,hv⟩,rfl⟩

def matchingCoordinateEquiv (M : Graph V) (hM : Matching M) : MatchingVertex M ≃ V :=
  Equiv.ofBijective (matchingCoordinateMap M)
    ⟨matchingCoordinateMap_injective M hM,matchingCoordinateMap_surjective M⟩

theorem matchingCoordinateEquiv_edge (M : Graph V) (hM : Matching M) (e : M) :
    (Finset.univ.image fun i : Fin 2 => matchingCoordinateEquiv M hM (.inl (e,i))) = e.val.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact endpoint_mem e.val i
  · intro hv
    obtain ⟨i,hi⟩ := endpoint_surjective e.val v hv
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩

def coordinateReorder (M : Graph V) (order : M → Equiv.Perm (Fin 2)) :
    MatchingVertex M ≃ MatchingVertex M where
  toFun
    | .inl (e,i) => .inl (e,order e i)
    | .inr v => .inr v
  invFun
    | .inl (e,i) => .inl (e,(order e).symm i)
    | .inr v => .inr v
  left_inv := by intro x; cases x with
    | inl x => rcases x with ⟨e,i⟩; simp
    | inr v => rfl
  right_inv := by intro x; cases x with
    | inl x => rcases x with ⟨e,i⟩; simp
    | inr v => rfl

def coverOrder (C : Finset V) (e : Edge V) : Equiv.Perm (Fin 2) :=
  if endpoint e 0 ∈ C then Equiv.refl _ else Equiv.swap 0 1

def orientedEndpoint (C : Finset V) (e : Edge V) (i : Fin 2) : V :=
  endpoint e (coverOrder C e i)

/-- After orientation, a crossing benchmark pair always places its center
first. Roots and internal pairs may retain either orientation. -/
theorem oriented_center_first (C : Finset V) (e : Edge V) :
    orientedEndpoint C e 1 ∈ C → orientedEndpoint C e 0 ∈ C := by
  by_cases h0 : endpoint e 0 ∈ C
  · simp [orientedEndpoint,coverOrder,h0]
  · simp [orientedEndpoint,coverOrder,h0]

def coveredMatchingCoordinateEquiv (M : Graph V) (hM : Matching M) (C : Finset V) :
    MatchingVertex M ≃ V :=
  (coordinateReorder M (fun e => coverOrder C e.val)).trans (matchingCoordinateEquiv M hM)

theorem coveredMatchingCoordinateEquiv_pair (M : Graph V) (hM : Matching M)
    (C : Finset V) (e : M) (i : Fin 2) :
    coveredMatchingCoordinateEquiv M hM C (.inl (e,i)) = orientedEndpoint C e.val i := rfl

theorem coveredMatchingCoordinateEquiv_unmatched (M : Graph V) (hM : Matching M)
    (C : Finset V) (v : {v : V // v ∉ covered M}) :
    coveredMatchingCoordinateEquiv M hM C (.inr v)=v.val := rfl

end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.matchingCoordinateEquiv
#print axioms RobustMatching.R7SupportFlowMap.matchingCoordinateEquiv_edge
#print axioms RobustMatching.R7SupportFlowMap.coveredMatchingCoordinateEquiv
#print axioms RobustMatching.R7SupportFlowMap.oriented_center_first
