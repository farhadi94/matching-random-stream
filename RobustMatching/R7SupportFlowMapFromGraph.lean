import RobustMatching.R7SupportFlowMapCoordinates
import RobustMatching.R7SupportFlowMapMatching

/-! Construct typed endpoint coordinates from an actual matching, vertex
cover and available-edge set. No class-count identities are assumed. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R2Cut RobustMatching.R7ReductionCertificate

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

def actualPairKind (C : Finset V) (available : Graph V) (e : Edge V) : PairKind :=
  if orientedEndpoint C e 0 ∈ C then
    if orientedEndpoint C e 1 ∈ C then
      if e ∈ available then .internalAvailable else .internalMissing
    else if e ∈ available then .gate else .missing
  else .root

def coordinatesFromMatching (M : Graph V) (hM : Matching M)
    (C : Finset V) (available : Graph V) (bin : V → Fin q) (mask : V → Fin 4) :
    Coordinates M {v : V // v ∉ covered M} q where
  kind e := actualPairKind C available e.val
  unmatchedCenter v := decide (v.val ∈ C)
  bin v := bin (coveredMatchingCoordinateEquiv M hM C v)
  mask v := mask (coveredMatchingCoordinateEquiv M hM C v)

def IsCenterColumn {q} : Column q → Prop
  | .center _ => True
  | _ => False

def IsVertexColumn {q} : Column q → Prop
  | .center _ | .outside _ => True
  | _ => False

theorem vertexColumn_is_vertex {B U : Type*} (d : Coordinates B U q)
    (v : Vertex B U) : IsVertexColumn (vertexColumn d v) := by
  cases v with
  | inl x =>
    rcases x with ⟨i,s⟩
    cases hk : d.kind i <;> by_cases hs : s=0 <;>
      simp [vertexColumn,hk,hs,leftColumn,rightColumn,IsVertexColumn]
  | inr u => cases hu : d.unmatchedCenter u <;> simp [vertexColumn,hu,IsVertexColumn]

theorem actual_center_classification (M : Graph V) (hM : Matching M)
    (C : Finset V) (available : Graph V) (bin : V → Fin q) (mask : V → Fin 4)
    (v : MatchingVertex M) :
    IsCenterColumn (vertexColumn (coordinatesFromMatching M hM C available bin mask) v) ↔
      coveredMatchingCoordinateEquiv M hM C v ∈ C := by
  cases v with
  | inl x =>
    rcases x with ⟨e,s⟩
    have hfirst := oriented_center_first C e.val
    fin_cases s <;>
      by_cases h0 : orientedEndpoint C e.val 0 ∈ C <;>
      by_cases h1 : orientedEndpoint C e.val 1 ∈ C <;>
      by_cases ha : e.val ∈ available <;>
      simp [vertexColumn,coordinatesFromMatching,actualPairKind,h0,h1,ha,
        leftColumn,rightColumn,IsCenterColumn,coveredMatchingCoordinateEquiv_pair] at *
  | inr u =>
    simp [vertexColumn,coordinatesFromMatching,IsCenterColumn,
      coveredMatchingCoordinateEquiv_unmatched]
    split_ifs <;> simp_all

theorem actual_vertex_bin (M : Graph V) (hM : Matching M)
    (C : Finset V) (available : Graph V) (bin : V → Fin q) (mask : V → Fin 4)
    (v : MatchingVertex M) :
    (coordinatesFromMatching M hM C available bin mask).bin v =
      bin (coveredMatchingCoordinateEquiv M hM C v) := rfl

end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.actual_center_classification
