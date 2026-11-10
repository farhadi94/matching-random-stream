import RobustMatching.R7ClosedRepairTypedBenchmark
import RobustMatching.R7SupportFlowMapFromGraph

/-! Explicit refinement of actual matching coordinates into the canonical
typed repair labels. Pair kinds and unmatched-cover flags determine the
fibers; no class-count or vertex-labeling bijection is assumed. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RobustMatching.R7ClosedRepair.TypedLabeling
open RobustMatching.R7SupportFlowMap RobustMatching.R7ReductionCertificate

variable {B U : Type*} {q : ℕ}

abbrev PairFiber (d : Coordinates B U q) (k : PairKind) := {b : B // d.kind b = k}
abbrev CenterUnmatched (d : Coordinates B U q) := {u : U // d.unmatchedCenter u = true}
abbrev OutsideUnmatched (d : Coordinates B U q) := {u : U // d.unmatchedCenter u = false}

abbrev CanonicalCenters (d : Coordinates B U q) :=
  RobustMatching.R7ClosedRepair.Typed.Centers (PairFiber d .gate) (PairFiber d .missing) (CenterUnmatched d)
    (PairFiber d .internalAvailable) (PairFiber d .internalMissing)
abbrev CanonicalOutsides (d : Coordinates B U q) :=
  RobustMatching.R7ClosedRepair.Typed.Outsides (PairFiber d .root) (PairFiber d .missing) (PairFiber d .gate)
    (OutsideUnmatched d)
abbrev CanonicalVertex (d : Coordinates B U q) := CanonicalCenters d ⊕ CanonicalOutsides d
abbrev CanonicalBenchmark (d : Coordinates B U q) :=
  RobustMatching.R7ClosedRepair.Typed.Benchmarks (PairFiber d .root) (PairFiber d .gate) (PairFiber d .missing)
    (PairFiber d .internalAvailable) (PairFiber d .internalMissing)

def boolIndex : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := if i = 0 then false else true
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def benchmarkForget (d : Coordinates B U q) : CanonicalBenchmark d → B
  | .inl r => r.val
  | .inr (.inl g) => g.val
  | .inr (.inr (.inl m)) => m.val
  | .inr (.inr (.inr (.inl i))) => i.val
  | .inr (.inr (.inr (.inr j))) => j.val

def benchmarkRefine (d : Coordinates B U q) (b : B) : CanonicalBenchmark d :=
  match hk : d.kind b with
  | .root => .inl ⟨b,hk⟩
  | .gate => .inr (.inl ⟨b,hk⟩)
  | .missing => .inr (.inr (.inl ⟨b,hk⟩))
  | .internalAvailable => .inr (.inr (.inr (.inl ⟨b,hk⟩)))
  | .internalMissing => .inr (.inr (.inr (.inr ⟨b,hk⟩)))

def benchmarkFiberEquiv (d : Coordinates B U q) : CanonicalBenchmark d ≃ B where
  toFun := benchmarkForget d
  invFun := benchmarkRefine d
  left_inv := by
    intro z
    rcases z with ⟨r,hr⟩ | ⟨g,hg⟩ | ⟨m,hm⟩ | ⟨i,hi⟩ | ⟨j,hj⟩ <;>
      simp only [benchmarkForget, benchmarkRefine]
    all_goals split <;> (try simp_all) <;> grind
  right_inv := by
    intro b
    unfold benchmarkRefine
    split <;> rfl

def coordinateMap (d : Coordinates B U q) : CanonicalVertex d → Vertex B U
  | .inl (.inl g) => .inl (g.val,0)
  | .inl (.inr (.inl m)) => .inl (m.val,0)
  | .inl (.inr (.inr (.inl p))) => .inr p.val
  | .inl (.inr (.inr (.inr (.inl i)))) => .inl (i.1.val,boolIndex i.2)
  | .inl (.inr (.inr (.inr (.inr j)))) => .inl (j.1.val,boolIndex j.2)
  | .inr (.inl r) => .inl (r.1.val,boolIndex r.2)
  | .inr (.inr (.inl m)) => .inl (m.val,1)
  | .inr (.inr (.inr (.inl g))) => .inl (g.val,1)
  | .inr (.inr (.inr (.inr u))) => .inr u.val

def coordinateRefine (d : Coordinates B U q) : Vertex B U → CanonicalVertex d
  | .inl (b,t) =>
      match hk : d.kind b with
      | .root => .inr (.inl (⟨b,hk⟩,boolIndex.symm t))
      | .gate => if t = 0 then .inl (.inl ⟨b,hk⟩)
          else .inr (.inr (.inr (.inl ⟨b,hk⟩)))
      | .missing => if t = 0 then .inl (.inr (.inl ⟨b,hk⟩))
          else .inr (.inr (.inl ⟨b,hk⟩))
      | .internalAvailable => .inl (.inr (.inr (.inr (.inl (⟨b,hk⟩,boolIndex.symm t)))))
      | .internalMissing => .inl (.inr (.inr (.inr (.inr (⟨b,hk⟩,boolIndex.symm t)))))
  | .inr u => if hu : d.unmatchedCenter u = true then
      .inl (.inr (.inr (.inl ⟨u,hu⟩)))
    else .inr (.inr (.inr (.inr ⟨u,by cases h : d.unmatchedCenter u <;> simp_all⟩)))

theorem coordinate_left_inverse (d : Coordinates B U q) :
    Function.LeftInverse (coordinateRefine d) (coordinateMap d) := by
  intro v
  rcases v with c | x
  · rcases c with ⟨g,hg⟩ | ⟨m,hm⟩ | ⟨p,hp⟩ | ⟨⟨i,hi⟩,t⟩ | ⟨⟨j,hj⟩,t⟩ <;>
      simp only [coordinateMap, coordinateRefine]
    all_goals split <;> (try simp_all) <;> grind
  · rcases x with ⟨⟨r,hr⟩,t⟩ | ⟨m,hm⟩ | ⟨g,hg⟩ | ⟨u,hu⟩ <;>
      simp only [coordinateMap, coordinateRefine]
    all_goals split <;> (try simp_all) <;> grind

theorem coordinate_right_inverse (d : Coordinates B U q) :
    Function.RightInverse (coordinateRefine d) (coordinateMap d) := by
  intro v
  rcases v with ⟨b,t⟩ | u
  · dsimp only [coordinateRefine]
    split <;> fin_cases t <;> simp [coordinateMap, boolIndex]
  · dsimp only [coordinateRefine]
    split <;> rfl

/-- The actual endpoint-coordinate partition is refined by pair-kind
fibers and the unmatched cover flag, preserving every individual vertex. -/
def coordinateEquiv (d : Coordinates B U q) : CanonicalVertex d ≃ Vertex B U where
  toFun := coordinateMap d
  invFun := coordinateRefine d
  left_inv := coordinate_left_inverse d
  right_inv := coordinate_right_inverse d

theorem coordinate_endpoint (d : Coordinates B U q)
    (b : CanonicalBenchmark d) (t : Bool) :
    coordinateEquiv d (RobustMatching.R7ClosedRepair.Typed.endpoint (P := CenterUnmatched d) (U := OutsideUnmatched d) b t) =
      .inl (benchmarkFiberEquiv d b,boolIndex t) := by
  rcases b with r | g | m | i | j <;> cases t <;>
    rfl

def centerType (d : Coordinates B U q) : CanonicalCenters d → CenterType
  | .inl _ => .G
  | .inr (.inl _) => .M
  | .inr (.inr (.inl _)) => .P
  | .inr (.inr (.inr (.inl _))) => .I
  | .inr (.inr (.inr (.inr _))) => .J

def outsideType (d : Coordinates B U q) : CanonicalOutsides d → OutsideType
  | .inl _ => .S
  | .inr (.inl _) => .T
  | .inr (.inr (.inl _)) => .A
  | .inr (.inr (.inr _)) => .O

def canonicalColumn (d : Coordinates B U q) : CanonicalVertex d → Column q
  | .inl c => .center (d.bin (coordinateEquiv d (.inl c)),centerType d c)
  | .inr x => .outside (d.bin (coordinateEquiv d (.inr x)),outsideType d x,
      d.mask (coordinateEquiv d (.inr x)))

/-- Exact class, degree-bin and affine-arm-mask correspondence with the
semantic LP coordinates. -/
theorem coordinate_vertex_column (d : Coordinates B U q) (v : CanonicalVertex d) :
    vertexColumn d (coordinateEquiv d v) = canonicalColumn d v := by
  rcases v with c | x
  · rcases c with ⟨g,hg⟩ | ⟨m,hm⟩ | ⟨p,hp⟩ | ⟨⟨i,hi⟩,t⟩ | ⟨⟨j,hj⟩,t⟩
    all_goals simp [coordinateEquiv, coordinateMap, vertexColumn, canonicalColumn,
      centerType, leftColumn, rightColumn, *]
  · rcases x with ⟨⟨r,hr⟩,t⟩ | ⟨m,hm⟩ | ⟨g,hg⟩ | ⟨u,hu⟩
    all_goals simp [coordinateEquiv, coordinateMap, vertexColumn, canonicalColumn,
      outsideType, leftColumn, rightColumn, *]

theorem coordinate_is_center (d : Coordinates B U q) (v : CanonicalVertex d) :
    IsCenterColumn (vertexColumn d (coordinateEquiv d v)) ↔
      (match v with | .inl _ => True | .inr _ => False) := by
  rw [coordinate_vertex_column]
  cases v <;> simp [canonicalColumn, IsCenterColumn]

end RobustMatching.R7ClosedRepair.TypedLabeling
