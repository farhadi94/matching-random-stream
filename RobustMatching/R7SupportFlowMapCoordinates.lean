import RobustMatching.R7SupportFlowMap
import RobustMatching.R7ReductionCertificateModel

/-! Canonical coordinates for a benchmark matching. Each benchmark index
has two distinct vertices; unmatched vertices form a disjoint summand.
The semantic LP equalities are derived from these actual endpoint records,
not postulated as a feasible-vector assumption. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate

inductive PairKind | root | gate | missing | internalAvailable | internalMissing
  deriving DecidableEq

def leftColumn {q} (k : PairKind) (b : Fin q) (m : Fin 4) : Column q :=
  match k with
  | .root => .outside (b,.S,m)
  | .gate => .center (b,.G)
  | .missing => .center (b,.M)
  | .internalAvailable => .center (b,.I)
  | .internalMissing => .center (b,.J)

def rightColumn {q} (k : PairKind) (b : Fin q) (m : Fin 4) : Column q :=
  match k with
  | .root => .outside (b,.S,m)
  | .gate => .outside (b,.A,m)
  | .missing => .outside (b,.T,m)
  | .internalAvailable => .center (b,.I)
  | .internalMissing => .center (b,.J)

def orderedRoot {q} (x y : OutsideClass q) : Column q :=
  if outsideIndex x ≤ outsideIndex y then .root x y else .root y x

def orderedPair {q} (c e : CenterClass q) : Column q :=
  if centerIndex c ≤ centerIndex e then .pair c e else .pair e c

def pairColumn {q} (k : PairKind) (b0 b1 : Fin q) (m0 m1 : Fin 4) : Column q :=
  match k with
  | .root => orderedRoot (b0,.S,m0) (b1,.S,m1)
  | .gate => .z
  | .missing => .missing (b0,.M) (b1,.T,m1)
  | .internalAvailable => orderedPair (b0,.I) (b1,.I)
  | .internalMissing => orderedPair (b0,.J) (b1,.J)

def pairWeight : PairKind → ℝ | .gate => 0 | _ => 1
def internalWeight : PairKind → ℝ
  | .internalAvailable | .internalMissing => 1 | _ => 0

/-- Every actual benchmark pair contributes exactly one normalization unit
and zero to every endpoint-balance row. Canonical endpoint ordering does
not change either incidence. -/
theorem benchmark_eq_balance {q} (k : PairKind) (b0 b1 : Fin q)
    (m0 m1 : Fin 4) (r : EqRow q) :
    (coeffEq r (leftColumn k b0 m0) : ℝ)+
      (coeffEq r (rightColumn k b1 m1) : ℝ)+
      pairWeight k*(coeffEq r (pairColumn k b0 b1 m0 m1) : ℝ)+
      internalWeight k*(coeffEq r .z : ℝ) = (rhsEq r : ℝ) := by
  cases k <;> cases r <;>
    simp [leftColumn,rightColumn,pairColumn,pairWeight,internalWeight,
      orderedRoot,orderedPair,coeffEq,eqTerms,coeff,rhsEq] <;>
    split_ifs <;> simp_all [coeff]

theorem unmatched_eq_zero {q} (b : Fin q) (m : Fin 4) (center : Bool)
    (r : EqRow q) :
    (coeffEq r (if center then .center (b,.P) else .outside (b,.O,m)) : ℝ)=0 := by
  cases center <;> cases r <;> simp [coeffEq,eqTerms,coeff]

theorem reference_eq_zero {q} (c e : CenterClass q) (x : OutsideClass q)
    (r : EqRow q) :
    coeffEq r (.cross c x)=0 ∧ coeffEq r (.internal c e)=0 := by
  simp [coeffEq,eqTerms,coeff]

section Coordinates
variable {B U : Type*} [Fintype B] [Fintype U]
  [DecidableEq B] [DecidableEq U] {q : ℕ}

abbrev Vertex (B U : Type*) := (B × Fin 2) ⊕ U

structure Coordinates (B U : Type*) (q : ℕ) where
  kind : B → PairKind
  unmatchedCenter : U → Bool
  bin : Vertex B U → Fin q
  mask : Vertex B U → Fin 4

def vertexColumn (d : Coordinates B U q) : Vertex B U → Column q
  | .inl (i,s) => if s=0 then
      leftColumn (d.kind i) (d.bin (.inl (i,s))) (d.mask (.inl (i,s))) else
      rightColumn (d.kind i) (d.bin (.inl (i,s))) (d.mask (.inl (i,s)))
  | .inr u => if d.unmatchedCenter u then .center (d.bin (.inr u),.P)
      else .outside (d.bin (.inr u),.O,d.mask (.inr u))

def benchmarkColumn (d : Coordinates B U q) (i : B) : Column q :=
  pairColumn (d.kind i) (d.bin (.inl (i,0))) (d.bin (.inl (i,1)))
    (d.mask (.inl (i,0))) (d.mask (.inl (i,1)))

theorem coordinate_eq_balance (d : Coordinates B U q) (r : EqRow q) :
    (∑ v : Vertex B U, (coeffEq r (vertexColumn d v) : ℝ))+
      (∑ i, pairWeight (d.kind i)*(coeffEq r (benchmarkColumn d i) : ℝ))+
      (∑ i, internalWeight (d.kind i))*(coeffEq r .z : ℝ) =
      (Fintype.card B : ℝ)*(rhsEq r : ℝ) := by
  have hu : (∑ u : U, (coeffEq r (vertexColumn d (.inr u)) : ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro u _
    exact unmatched_eq_zero _ _ _ r
  rw [Fintype.sum_sum_type,hu,add_zero,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,vertexColumn,if_pos rfl]
  rw [Finset.sum_mul,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  calc
    _ = ∑ _i : B, (rhsEq r : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact benchmark_eq_balance _ _ _ _ _ r
    _ = (Fintype.card B : ℝ)*(rhsEq r : ℝ) := by simp

end Coordinates
end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.benchmark_eq_balance
#print axioms RobustMatching.R7SupportFlowMap.coordinate_eq_balance
