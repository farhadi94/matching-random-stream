import RandomOrderMatching.Certificates.DegreeProfile.Data
import RandomOrderMatching.Certificates.DegreeProfile.IntegerEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RandomOrderMatching.Certificates.DegreeProfile

def outsideAllowedInt {q} (g : Fin (q+1) → ℤ) (x : OutsideClass q) : Prop :=
  match x.2.1 with
  | .A => x.2.2.val < 2
  | .O => gUpper g x.1 ≤ 256 → x.2.2.val = 0
  | _ => True
instance {q} (g : Fin (q+1) → ℤ) (x : OutsideClass q) :
    Decidable (outsideAllowedInt g x) := by unfold outsideAllowedInt; split <;> infer_instance

def allowedInt {q} (g : Fin (q+1) → ℤ) : Column q → Prop
  | .center _ => True
  | .outside x => outsideAllowedInt g x
  | .cross c x => outsideAllowedInt g x ∧ gLower g c.1+gLower g x.1 ≤ 512
  | .internal c e => centerIndex c ≤ centerIndex e ∧ gLower g c.1+gLower g e.1 ≤ 512
  | .root x y => outsideAllowedInt g x ∧ outsideAllowedInt g y ∧
      x.2.1 = .S ∧ y.2.1 = .S ∧ outsideIndex x ≤ outsideIndex y ∧
      51199999488 ≤ 100000000*(gUpper g x.1+gUpper g y.1)
  | .missing c x => outsideAllowedInt g x ∧ c.2 = .M ∧ x.2.1 = .T ∧
      51199999488 ≤ 100000000*(gUpper g c.1+gUpper g x.1)
  | .pair c e => centerIndex c ≤ centerIndex e ∧ c.2 = e.2 ∧
      ((c.2 = .I ∧ gLower g c.1+gLower g e.1 ≤ 512) ∨
       (c.2 = .J ∧ 51199999488 ≤ 100000000*(gUpper g c.1+gUpper g e.1)))
  | .z | .value => True
instance {q} (g : Fin (q+1) → ℤ) (c : Column q) : Decidable (allowedInt g c) := by
  unfold allowedInt; split <;> infer_instance

theorem half_grid (a : ℤ) : (a:ℚ)/512 ≤ 1/2 ↔ a ≤ 256 := by
  have h : (a:ℚ)/512 ≤ 1/2 ↔ (a:ℚ) ≤ 256 := by constructor <;> intro h <;> linarith
  rw [h]
  norm_cast
theorem lower_grid (a b : ℤ) : (a:ℚ)/512+(b:ℚ)/512 ≤ 1 ↔ a+b ≤ 512 := by
  have h : (a:ℚ)/512+(b:ℚ)/512 ≤ 1 ↔ (a:ℚ)+(b:ℚ) ≤ 512 := by
    constructor <;> intro h <;> linarith
  rw [h]
  norm_cast
theorem upper_grid (a b : ℤ) :
    (1-1/100000000:ℚ) ≤ (a:ℚ)/512+(b:ℚ)/512 ↔ 51199999488 ≤ 100000000*(a+b) := by
  have h : (1-1/100000000:ℚ) ≤ (a:ℚ)/512+(b:ℚ)/512 ↔
      (51199999488:ℚ) ≤ 100000000*((a:ℚ)+(b:ℚ)) := by
    constructor <;> intro h <;> linarith
  rw [h]
  norm_cast

theorem outside_allowed_equiv {q} (g : Fin (q+1) → ℤ) (x : OutsideClass q) :
    outsideAllowed (reflectedData g) x ↔ outsideAllowedInt g x := by
  rcases x with ⟨i,t,k⟩
  cases t with
  | S => rfl
  | T => rfl
  | A => rfl
  | O =>
    change ((g i.succ:ℚ)/512 ≤ 1/2 → k.val=0) ↔ (g i.succ ≤ 256 → k.val=0)
    rw [half_grid]

theorem allowed_equiv {q} (g : Fin (q+1) → ℤ) (c : Column q) :
    columnAllowed (reflectedData g) c ↔ allowedInt g c := by
  cases c <;> simp only [columnAllowed,allowedInt]
  all_goals try simp only [outside_allowed_equiv]
  all_goals simp only [lower,upper,reflectedData,gLower,gUpper,lower_grid,upper_grid]

def checkUpTo : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n+1, f => checkUpTo n f && f n

theorem checkUpTo_iff (n : ℕ) (f : ℕ → Bool) :
    checkUpTo n f = true ↔ ∀ i<n,f i=true := by
  induction n with
  | zero => simp [checkUpTo]
  | succ n ih =>
    simp only [checkUpTo,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨h,hn⟩ i hi
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
      · exact h i hlt
      · simpa [heq] using hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)),h n (Nat.lt_succ_self n)⟩

end RandomOrderMatching.Certificates.DegreeProfile
