import RobustMatching.R7ReductionCertificateCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RobustMatching.R7ReductionCertificate.Concrete
open RobustMatching.R7ReductionCertificate

def centerAt (n : ℕ) : CenterClass 152 :=
  (⟨n/5%152,Nat.mod_lt _ (by decide)⟩,
    match n%5 with | 0 => .G | 1 => .M | 2 => .P | 3 => .I | _ => .J)
def outsideAt (n : ℕ) : OutsideClass 152 :=
  (⟨n/16%152,Nat.mod_lt _ (by decide)⟩,
    (match n/4%4 with | 0 => .S | 1 => .T | 2 => .A | _ => .O),
    ⟨n%4,Nat.mod_lt _ (by decide)⟩)

theorem centerIndex_bound (c : CenterClass 152) : centerIndex c < 760 := by
  rcases c with ⟨i,t⟩
  have hi := i.isLt
  cases t <;> simp only [centerIndex,CenterType.index] <;> omega
theorem outsideIndex_bound (x : OutsideClass 152) : outsideIndex x < 2432 := by
  rcases x with ⟨i,t,k⟩
  have hi := i.isLt
  have hk := k.isLt
  cases t <;> simp only [outsideIndex,OutsideType.index] <;> omega

theorem centerAt_index (c : CenterClass 152) : centerAt (centerIndex c) = c := by
  rcases c with ⟨i,t⟩
  have hi := i.isLt
  cases t <;> simp [centerAt,centerIndex,CenterType.index,Nat.add_div,Nat.add_mod,
    Nat.mul_mod,Nat.mod_eq_of_lt i.isLt]

theorem outsideAt_index (x : OutsideClass 152) : outsideAt (outsideIndex x) = x := by
  rcases x with ⟨i,t,k⟩
  have hi := i.isLt
  have hmul : 16*i.val/4%4=0 := by omega
  cases t <;> fin_cases k <;> simp [hmul,outsideAt,outsideIndex,OutsideType.index,
    Nat.add_div,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt i.isLt]

def checkColumn (c : Column 152) : Bool :=
  decide (allowedInt (fun i => gridNumerator i.val) c →
    0 ≤ intSlack (fun i => gridNumerator i.val) dualDenominator dualEqNumerator dualLeNumerator c)

def checkCenters := checkUpTo 760 (fun i => checkColumn (.center (centerAt i)))
def checkOutside := checkUpTo 2432 (fun i => checkColumn (.outside (outsideAt i)))
def checkCross (i : ℕ) := checkUpTo 2432 (fun j => checkColumn (.cross (centerAt i) (outsideAt j)))
def checkInternal (i : ℕ) := checkUpTo 760 (fun j => checkColumn (.internal (centerAt i) (centerAt j)))
def checkRoot (i : ℕ) := checkUpTo 2432 (fun j => checkColumn (.root (outsideAt i) (outsideAt j)))
def checkMissing (i : ℕ) := checkUpTo 2432 (fun j => checkColumn (.missing (centerAt i) (outsideAt j)))
def checkPair (i : ℕ) := checkUpTo 760 (fun j => checkColumn (.pair (centerAt i) (centerAt j)))

def checkRange (lo count : ℕ) (f : ℕ → Bool) : Bool := checkUpTo count (fun i => f (lo+i))
theorem checkRange_concat (lo a b : ℕ) (f : ℕ → Bool)
    (ha : checkRange lo a f = true) (hb : checkRange (lo+a) b f = true) :
    checkRange lo (a+b) f = true := by
  apply (checkUpTo_iff _ _).2
  intro i hi
  by_cases hia : i<a
  · exact (checkUpTo_iff _ _).1 ha i hia
  · have hj : i-a<b := by omega
    have hh := (checkUpTo_iff _ _).1 hb (i-a) hj
    have he : lo+a+(i-a)=lo+i := by omega
    simpa only [he] using hh

theorem checked_index {A : Type*} (n : ℕ) (encode : A → ℕ) (decode : ℕ → A)
    (hbound : ∀ a,encode a<n) (hinv : ∀ a,decode (encode a)=a)
    (P : A → Prop) [∀ a,Decidable (P a)]
    (h : checkUpTo n (fun i => decide (P (decode i))) = true) : ∀ a,P a := by
  intro a
  have hh := (checkUpTo_iff _ _).1 h (encode a) (hbound a)
  have hp := of_decide_eq_true hh
  simpa only [hinv a] using hp

end RobustMatching.R7ReductionCertificate.Concrete
