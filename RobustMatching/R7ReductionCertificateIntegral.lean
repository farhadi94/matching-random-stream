import RobustMatching.R7ReductionCertificateModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RobustMatching.R7ReductionCertificate

def reflectedData {q} (g : Fin (q+1) → ℤ) : ProfileData q where
  grid i := (g i:ℚ)/512
  alpha := 11/20
  omega := 550001/1000000
  lam := 1/100000000
  cap := 1/100
  massBound := 267

def gLower {q} (g : Fin (q+1) → ℤ) (i : Fin q) := g i.castSucc
def gUpper {q} (g : Fin (q+1) → ℤ) (i : Fin q) := g i.succ
def denominator {q} (g : Fin (q+1) → ℤ) (x : OutsideClass q) : ℤ :=
  max 512 (100*(512-gLower g x.1))
def scale {q} (g : Fin (q+1) → ℤ) : Column q → ℤ
  | .center _ | .outside _ => 1024000000
  | .cross _ x => 1000000*denominator g x
  | .root _ _ | .missing _ _ => 100000000
  | .pair _ _ => 2000000
  | _ => 1
def intCost {q} : Column q → ℤ | .value => 1 | _ => 0

def primaryInt : CenterType → ℤ | .G => 450000 | _ => 1000000
def secondaryInt : CenterType → ℤ | .M | .J => 550001 | .P => 1000000 | _ => 0
def capInt : OutsideType → ℤ | .S | .T => 550001 | _ => 1000000
def centerInt : CenterType → ℤ | .G => 1550000 | .M => 449999 | _ => 0
def outsideInt {q} (x : OutsideClass q) : ℤ :=
  if x.2.1 = .A then (if x.2.2.val % 2 = 1 then 450000 else 0)
  else (if x.2.2.val % 2 = 1 then capInt x.2.1 else 0)+
       (if x.2.2.val / 2 % 2 = 1 then 1000000 else 0)
def edgeInt {q} (c : CenterClass q) (x : OutsideClass q) : ℤ :=
  if x.2.1 = .A then (if x.2.2.val % 2 = 0 then secondaryInt c.2 else 0)
  else (if x.2.2.val % 2 = 0 then primaryInt c.2 else 0)+
       (if x.2.2.val / 2 % 2 = 0 then secondaryInt c.2 else 0)

def eqIntDot {q} (y : EqRow q → ℤ) : Column q → ℤ
  | .center c => (if c.2 = .G ∨ c.2 = .M then y .normalization else 0)+
      match c.2 with
      | .G => y .availableBalance | .M => -y (.missingCenter c)
      | .I | .J => -y (.internalCenter c) | .P => 0
  | .outside x => match x.2.1 with
      | .S => -y (.rootEndpoint x) | .T => -y (.missingOutside x)
      | .A => -y .availableBalance | .O => 0
  | .root x z => y .normalization+y (.rootEndpoint x)+y (.rootEndpoint z)
  | .missing c x => y (.missingCenter c)+y (.missingOutside x)
  | .pair c e => y .internalCount+y (.internalCenter c)+y (.internalCenter e)
  | .z => y .normalization-y .internalCount
  | _ => 0

def leIntDot {q} (g : Fin (q+1) → ℤ) (y : LeRow q → ℤ) : Column q → ℤ
  | .center c => y (.centerLower c)*(gLower g c.1*2000000)-
      y (.centerUpper c)*(gUpper g c.1*2000000)+
      (y .baseValue+y .baseOne+y .mass)*1024000000+y .phase*(centerInt c.2*512)
  | .outside x => y (.outsideLower x)*(gLower g x.1*2000000)-
      y (.outsideUpper x)*(gUpper g x.1*2000000)+
      y .mass*(if x.1.val=0 ∧ x.2.1 = .O then 0 else 1024000000)+
      y .phase*(outsideInt x*512)
  | .cross c x => (-y (.centerLower c)+y (.centerUpper c)-
      y (.outsideLower x)+y (.outsideUpper x)+y .mass-
      (if x.2.1 = .S then y .rootMoment else 0)-
      (if c.2 = .M then y .missingMoment else 0)-
      (if x.2.1 = .T then y .missingMoment else 0))*(1000000*denominator g x)+
      y .phase*(25600*edgeInt c x)
  | .internal c e => -y (.centerLower c)+y (.centerUpper c)-
      y (.centerLower e)+y (.centerUpper e)+y .mass-
      (if c.2 = .M then y .missingMoment else 0)-
      (if e.2 = .M then y .missingMoment else 0)
  | .root _ _ => y .mass*100000000+y .phase*22499950+y .rootMoment*99999999
  | .missing _ _ => y .mass*100000000+y .missingMoment*99999999
  | .pair c _ => y .mass*2000000+y .phase*(if c.2 = .I then 1000000 else 449999)
  | .z => y .mass
  | .value => -y .baseValue+y .valueOne+y .mass-y .phase

def intSlack {q} (g : Fin (q+1) → ℤ) (D : ℤ)
    (ye : EqRow q → ℤ) (yl : LeRow q → ℤ) (c : Column q) : ℤ :=
  intCost c*scale g c*D-eqIntDot ye c*scale g c-leIntDot g yl c

theorem denominator_pos {q} (g : Fin (q+1) → ℤ) (x : OutsideClass q) :
    0 < denominator g x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem scale_pos {q} (g : Fin (q+1) → ℤ) (c : Column q) : 0 < scale g c := by
  cases c <;> simp only [scale,denominator] <;> positivity

theorem capped_denominator_identity (g : ℤ) :
    max (1/100:ℚ) (1-(g:ℚ)/512) = (max 512 (100*(512-g)):ℤ)/51200 := by
  by_cases h : (512:ℤ) ≤ 100*(512-g)
  · rw [max_eq_right h]
    have hq : (512:ℚ) ≤ 100*(512-(g:ℚ)) := by exact_mod_cast h
    rw [max_eq_right (show (1/100:ℚ) ≤ 1-(g:ℚ)/512 by linarith)]
    push_cast
    ring
  · have hi : 100*(512-g) ≤ (512:ℤ) := by omega
    rw [max_eq_left hi]
    have hq : 100*(512-(g:ℚ)) ≤ (512:ℚ) := by exact_mod_cast hi
    rw [max_eq_left (show 1-(g:ℚ)/512 ≤ (1/100:ℚ) by linarith)]
    norm_num

theorem primary_identity {q} (g : Fin (q+1) → ℤ) (t : CenterType) :
    primaryRate (reflectedData g) t = (primaryInt t:ℚ)/1000000 := by
  cases t <;> norm_num [primaryRate,reflectedData,inactive,primaryInt] <;> decide
theorem secondary_identity {q} (g : Fin (q+1) → ℤ) (t : CenterType) :
    secondaryRate (reflectedData g) t = (secondaryInt t:ℚ)/1000000 := by
  cases t <;> norm_num [secondaryRate,reflectedData,secondaryInt] <;> decide
theorem cap_identity {q} (g : Fin (q+1) → ℤ) (t : OutsideType) :
    primaryCap (reflectedData g) t = (capInt t:ℚ)/1000000 := by
  cases t <;> norm_num [primaryCap,reflectedData,capInt] <;> decide
theorem center_identity {q} (g : Fin (q+1) → ℤ) (t : CenterType) :
    centerCredit (reflectedData g) t = (centerInt t:ℚ)/2000000 := by
  cases t <;> norm_num [centerCredit,reflectedData,centerInt] <;> decide

theorem outside_identity {q} (g : Fin (q+1) → ℤ) (x : OutsideClass q) :
    outsideCredit (reflectedData g) x = (outsideInt x:ℚ)/2000000 := by
  unfold outsideCredit outsideInt
  rw [cap_identity]
  split_ifs <;> simp_all [inactive,reflectedData] <;> push_cast <;> ring

theorem edge_identity {q} (g : Fin (q+1) → ℤ) (c : CenterClass q) (x : OutsideClass q) :
    edgeCredit (reflectedData g) c x =
      (25600*edgeInt c x:ℤ)/(1000000*denominator g x:ℤ) := by
  have hd : (denominator g x:ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (denominator_pos g x))
  have he : max (reflectedData g).cap (1-lower (reflectedData g) x.1) =
      (denominator g x:ℚ)/51200 := by
    simpa [reflectedData,lower,denominator,gLower] using capped_denominator_identity (gLower g x.1)
  unfold edgeCredit edgeInt
  simp only [primary_identity,secondary_identity]
  rw [he]
  split_ifs <;> push_cast <;> field_simp [hd] <;> ring


 theorem eq_dot_identity {q} (D : ℤ) (hD : D ≠ 0)
    (y : EqRow q → ℤ) (c : Column q) :
    (D:ℚ)*dot (eqTerms c) (fun r => (y r:ℚ)/D) = (eqIntDot y c:ℚ) := by
  have hd : (D:ℚ) ≠ 0 := by exact_mod_cast hD
  cases c with
  | center c =>
    rcases c with ⟨i,t⟩
    cases t <;> simp [eqTerms,eqIntDot,dot,reduceCtorEq] <;>
      push_cast <;> field_simp [hd] <;> ring
  | outside x =>
    rcases x with ⟨i,t,k⟩
    cases t <;> simp [eqTerms,eqIntDot,dot,reduceCtorEq] <;>
      push_cast <;> field_simp [hd] <;> ring
  | cross c x => simp [eqTerms,eqIntDot,dot]
  | internal c e => simp [eqTerms,eqIntDot,dot]
  | root x z => simp [eqTerms,eqIntDot,dot] <;> push_cast <;> field_simp [hd] <;> ring
  | missing c x => simp [eqTerms,eqIntDot,dot] <;> push_cast <;> field_simp [hd] <;> ring
  | pair c e => simp [eqTerms,eqIntDot,dot] <;> push_cast <;> field_simp [hd] <;> ring
  | z => simp [eqTerms,eqIntDot,dot] <;> push_cast <;> field_simp [hd] <;> ring
  | value => simp [eqTerms,eqIntDot,dot]

 theorem le_dot_identity {q} (g : Fin (q+1) → ℤ) (D : ℤ) (hD : D ≠ 0)
    (y : LeRow q → ℤ) (c : Column q) :
    (scale g c:ℚ)*(D:ℚ)*dot (leTerms (reflectedData g) c) (fun r => (y r:ℚ)/D) =
      (leIntDot g y c:ℚ) := by
  have hd : (D:ℚ) ≠ 0 := by exact_mod_cast hD
  have hden (x : OutsideClass q) : (denominator g x:ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (denominator_pos g x))
  cases c <;> simp only [leTerms,dot]
  all_goals try simp only [center_identity,outside_identity,edge_identity]
  all_goals simp only [reflectedData,lower,upper,gLower,gUpper,leIntDot,scale]
  all_goals try split_ifs
  all_goals push_cast <;> field_simp [hd,hden] <;> ring

 theorem integer_slack_identity {q} (g : Fin (q+1) → ℤ) (D : ℤ) (hD : D ≠ 0)
    (ye : EqRow q → ℤ) (yl : LeRow q → ℤ) (c : Column q) :
    (scale g c:ℚ)*(D:ℚ)*slack (reflectedData g)
        (fun r => (ye r:ℚ)/D) (fun r => (yl r:ℚ)/D) c = (intSlack g D ye yl c:ℚ) := by
  have he := eq_dot_identity D hD ye c
  have hl := le_dot_identity g D hD yl c
  have hc : cost c = (intCost c:ℚ) := by cases c <;> rfl
  unfold slack intSlack
  push_cast
  rw [hc]
  linear_combination -(scale g c:ℚ)*he - hl

 theorem integer_slack_nonneg {q} (g : Fin (q+1) → ℤ) (D : ℤ) (hD : 0 < D)
    (ye : EqRow q → ℤ) (yl : LeRow q → ℤ) (c : Column q)
    (hi : 0 ≤ intSlack g D ye yl c) :
    0 ≤ slack (reflectedData g) (fun r => (ye r:ℚ)/D) (fun r => (yl r:ℚ)/D) c := by
  have hid := integer_slack_identity g D (ne_of_gt hD) ye yl c
  have hs : (0:ℚ) < (scale g c:ℚ)*(D:ℚ) := by
    exact mul_pos (by exact_mod_cast scale_pos g c) (by exact_mod_cast hD)
  have hn : (0:ℚ) ≤ (scale g c:ℚ)*(D:ℚ)*slack (reflectedData g)
      (fun r => (ye r:ℚ)/D) (fun r => (yl r:ℚ)/D) c := by
    rw [hid]
    exact_mod_cast hi
  exact nonneg_of_mul_nonneg_right hn hs

end RobustMatching.R7ReductionCertificate

#print axioms RobustMatching.R7ReductionCertificate.integer_slack_nonneg
