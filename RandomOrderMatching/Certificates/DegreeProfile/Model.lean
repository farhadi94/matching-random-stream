import Mathlib.Tactic
import Mathlib.Data.Fintype.Prod

/-! Exact semantic matrix for the internal-pair support profile.
No numerical certificate or graph feasibility is assumed in this model. -/
namespace RandomOrderMatching.Certificates.DegreeProfile

inductive CenterType | G | M | P | I | J
  deriving DecidableEq
inductive OutsideType | S | T | A | O
  deriving DecidableEq
instance : Fintype CenterType := ⟨{.G,.M,.P,.I,.J},by intro x; cases x <;> simp⟩
instance : Fintype OutsideType := ⟨{.S,.T,.A,.O},by intro x; cases x <;> simp⟩

abbrev CenterClass (q : ℕ) := Fin q × CenterType
abbrev OutsideClass (q : ℕ) := Fin q × OutsideType × Fin 4

structure ProfileData (q : ℕ) where
  grid : Fin (q+1) → ℚ
  alpha : ℚ
  omega : ℚ
  lam : ℚ
  cap : ℚ
  massBound : ℕ

def lower {q} (d : ProfileData q) (i : Fin q) := d.grid i.castSucc
def upper {q} (d : ProfileData q) (i : Fin q) := d.grid i.succ
def inactive {q} (d : ProfileData q) : ℚ := 1-d.alpha

def CenterType.index : CenterType → ℕ
  | .G => 0 | .M => 1 | .P => 2 | .I => 3 | .J => 4
def OutsideType.index : OutsideType → ℕ
  | .S => 0 | .T => 1 | .A => 2 | .O => 3
def centerIndex {q} (c : CenterClass q) := 5*c.1.val+c.2.index
def outsideIndex {q} (x : OutsideClass q) := 16*x.1.val+4*x.2.1.index+x.2.2.val

def outsideAllowed {q} (d : ProfileData q) (x : OutsideClass q) : Prop :=
  match x.2.1 with
  | .A => x.2.2.val < 2
  | .O => upper d x.1 ≤ 1/2 → x.2.2.val = 0
  | _ => True
instance {q} (d : ProfileData q) (x : OutsideClass q) :
    Decidable (outsideAllowed d x) := by unfold outsideAllowed; split <;> infer_instance

inductive Column (q : ℕ)
  | center (c : CenterClass q)
  | outside (x : OutsideClass q)
  | cross (c : CenterClass q) (x : OutsideClass q)
  | internal (c d : CenterClass q)
  | root (x y : OutsideClass q)
  | missing (c : CenterClass q) (x : OutsideClass q)
  | pair (c d : CenterClass q)
  | z | value
  deriving DecidableEq, Fintype

def columnAllowed {q} (d : ProfileData q) : Column q → Prop
  | .center _ => True
  | .outside x => outsideAllowed d x
  | .cross c x => outsideAllowed d x ∧ lower d c.1+lower d x.1 ≤ 1
  | .internal c e => centerIndex c ≤ centerIndex e ∧ lower d c.1+lower d e.1 ≤ 1
  | .root x y => outsideAllowed d x ∧ outsideAllowed d y ∧
      x.2.1 = .S ∧ y.2.1 = .S ∧ outsideIndex x ≤ outsideIndex y ∧
      1-d.lam ≤ upper d x.1+upper d y.1
  | .missing c x => outsideAllowed d x ∧ c.2 = .M ∧ x.2.1 = .T ∧
      1-d.lam ≤ upper d c.1+upper d x.1
  | .pair c e => centerIndex c ≤ centerIndex e ∧ c.2 = e.2 ∧
      ((c.2 = .I ∧ lower d c.1+lower d e.1 ≤ 1) ∨
       (c.2 = .J ∧ 1-d.lam ≤ upper d c.1+upper d e.1))
  | .z | .value => True
instance {q} (d : ProfileData q) (c : Column q) :
    Decidable (columnAllowed d c) := by unfold columnAllowed; split <;> infer_instance

inductive EqRow (q : ℕ)
  | normalization | internalCount
  | internalCenter (c : CenterClass q)
  | rootEndpoint (x : OutsideClass q)
  | missingOutside (x : OutsideClass q)
  | missingCenter (c : CenterClass q)
  | availableBalance
  deriving DecidableEq, Fintype

inductive LeRow (q : ℕ)
  | centerLower (c : CenterClass q) | centerUpper (c : CenterClass q)
  | outsideLower (x : OutsideClass q) | outsideUpper (x : OutsideClass q)
  | baseValue | baseOne | valueOne | rootMoment | missingMoment | mass | phase
  deriving DecidableEq, Fintype

def eqTerms {q} : Column q → List (EqRow q × ℚ)
  | .center c =>
      (if c.2 = .G ∨ c.2 = .M then [(.normalization,1)] else []) ++
      match c.2 with
      | .G => [(.availableBalance,1)]
      | .M => [(.missingCenter c,-1)]
      | .I | .J => [(.internalCenter c,-1)]
      | .P => []
  | .outside x => match x.2.1 with
      | .S => [(.rootEndpoint x,-1)]
      | .T => [(.missingOutside x,-1)]
      | .A => [(.availableBalance,-1)]
      | .O => []
  | .root x y => [(.normalization,1),(.rootEndpoint x,1),(.rootEndpoint y,1)]
  | .missing c x => [(.missingCenter c,1),(.missingOutside x,1)]
  | .pair c e => [(.internalCount,1),(.internalCenter c,1),(.internalCenter e,1)]
  | .z => [(.normalization,1),(.internalCount,-1)]
  | _ => []

def primaryRate {q} (d : ProfileData q) (t : CenterType) : ℚ :=
  if t = .G then inactive d else 1
def secondaryRate {q} (d : ProfileData q) (t : CenterType) : ℚ :=
  if t = .M ∨ t = .J then d.omega else if t = .P then 1 else 0
def primaryCap {q} (d : ProfileData q) (t : OutsideType) : ℚ :=
  if t = .S ∨ t = .T then d.omega else 1
def centerCredit {q} (d : ProfileData q) (t : CenterType) : ℚ :=
  if t = .G then (1+d.alpha)/2 else if t = .M then (1-d.omega)/2 else 0
def outsideCredit {q} (d : ProfileData q) (x : OutsideClass q) : ℚ :=
  if x.2.1 = .A then (if x.2.2.val % 2 = 1 then inactive d else 0)/2
  else ((if x.2.2.val % 2 = 1 then primaryCap d x.2.1 else 0)+
        (if x.2.2.val / 2 % 2 = 1 then 1 else 0))/2
def edgeCredit {q} (d : ProfileData q) (c : CenterClass q) (x : OutsideClass q) : ℚ :=
  let den := max d.cap (1-lower d x.1)
  if x.2.1 = .A then
    (if x.2.2.val % 2 = 0 then secondaryRate d c.2 else 0)/(2*den)
  else ((if x.2.2.val % 2 = 0 then primaryRate d c.2 else 0)+
        (if x.2.2.val / 2 % 2 = 0 then secondaryRate d c.2 else 0))/(2*den)

def leTerms {q} (d : ProfileData q) : Column q → List (LeRow q × ℚ)
  | .center c => [(.centerLower c,lower d c.1),(.centerUpper c,-upper d c.1),
      (.baseValue,1),(.baseOne,1),(.mass,1),(.phase,centerCredit d c.2)]
  | .outside x => [(.outsideLower x,lower d x.1),(.outsideUpper x,-upper d x.1),
      (.mass,if x.1.val = 0 ∧ x.2.1 = .O then 0 else 1),(.phase,outsideCredit d x)]
  | .cross c x => [(.centerLower c,-1),(.centerUpper c,1),
      (.outsideLower x,-1),(.outsideUpper x,1),(.mass,1),(.phase,edgeCredit d c x),
      (.rootMoment,if x.2.1 = .S then -1 else 0),
      (.missingMoment,-(if c.2 = .M then 1 else 0)-(if x.2.1 = .T then 1 else 0))]
  | .internal c e => [(.centerLower c,-1),(.centerUpper c,1),
      (.centerLower e,-1),(.centerUpper e,1),(.mass,1),
      (.missingMoment,-(if c.2 = .M then 1 else 0)-(if e.2 = .M then 1 else 0))]
  | .root x y => [(.mass,1),(.phase,(1-d.omega)/2),(.rootMoment,1-d.lam)]
  | .missing _ _ => [(.mass,1),(.missingMoment,1-d.lam)]
  | .pair c _ => [(.mass,1),(.phase,if c.2 = .I then 1/2 else (1-d.omega)/2)]
  | .z => [(.mass,1)]
  | .value => [(.baseValue,-1),(.valueOne,1),(.mass,1),(.phase,-1)]

def coeff {R : Type*} [DecidableEq R] : List (R × ℚ) → R → ℚ
  | [], _ => 0
  | (k,a)::tail, r => (if k=r then a else 0)+coeff tail r
def dot {R : Type*} : List (R × ℚ) → (R → ℚ) → ℚ
  | [], _ => 0
  | (k,a)::tail, y => y k*a+dot tail y

def coeffEq {q} (r : EqRow q) (c : Column q) := coeff (eqTerms c) r
def coeffLe {q} (d : ProfileData q) (r : LeRow q) (c : Column q) := coeff (leTerms d c) r
def rhsEq {q} : EqRow q → ℚ | .normalization => 1 | _ => 0
def rhsLe {q} (d : ProfileData q) : LeRow q → ℚ
  | .baseOne | .valueOne => 1 | .mass => d.massBound | _ => 0
def cost {q} : Column q → ℚ | .value => 1 | _ => 0
def slack {q} (d : ProfileData q) (ye : EqRow q → ℚ) (yl : LeRow q → ℚ)
    (c : Column q) : ℚ := cost c-dot (eqTerms c) ye-dot (leTerms d c) yl

open scoped BigOperators
theorem sum_coeff_eq_dot {R : Type*} [Fintype R] [DecidableEq R]
    (l : List (R × ℚ)) (y : R → ℚ) : (∑ r, y r*coeff l r) = dot l y := by
  induction l with
  | nil => simp [coeff,dot]
  | cons a l ih =>
    rcases a with ⟨k,a⟩
    simp [coeff,dot,mul_add,Finset.sum_add_distrib,ih,mul_ite]

theorem slack_iff_columns {q} (d : ProfileData q)
    (ye : EqRow q → ℚ) (yl : LeRow q → ℚ) (c : Column q) :
    0 ≤ slack d ye yl c ↔
      (∑ r,ye r*coeffEq r c)+(∑ r,yl r*coeffLe d r c) ≤ cost c := by
  simp only [coeffEq,coeffLe,sum_coeff_eq_dot]
  unfold slack
  constructor <;> intro h <;> linarith

end RandomOrderMatching.Certificates.DegreeProfile

#print axioms RandomOrderMatching.Certificates.DegreeProfile.slack_iff_columns
