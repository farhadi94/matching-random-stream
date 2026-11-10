import RobustMatching.R8RepairProbabilityLocalBudgets

/-! Cardinality and error accounting. Low unmatched leaves are not charged
an individual error and their number is unrestricted. -/
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RobustMatching.R8RepairProbability
open R7ClosedRepair R7ClosedRepair.Typed
variable {G M P I J R U : Type*}
variable [Fintype G] [Fintype M] [Fintype P] [Fintype I]
  [Fintype J] [Fintype R] [Fintype U]

def significant (w : Centers G M P I J→Outsides R M G U→ℝ) :
    Finset (Outsides R M G U) := Finset.univ.filter fun x=>¬lowUnmatched w x

def highLeaves (w : Centers G M P I J→Outsides R M G U→ℝ) : Finset U :=
  Finset.univ.filter fun u=>1<∑c,w c (.inr (.inr (.inr u)))

lemma highLeaves_card_le
    (w : Centers G M P I J→Outsides R M G U→ℝ)
    (hw : ∀c x,0≤w c x) (hrow : ∀c,∑x,w c x≤1) :
    ((highLeaves w).card:ℝ)≤(Fintype.card (Centers G M P I J):ℝ) := by
  calc
    _ = ∑u∈highLeaves w,(1:ℝ) := by simp
    _ ≤ ∑u∈highLeaves w,∑c,w c (.inr (.inr (.inr u))) :=
      Finset.sum_le_sum fun u hu=>le_of_lt (Finset.mem_filter.mp hu).2
    _ ≤ ∑u:U,∑c,w c (.inr (.inr (.inr u))) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun u _ _=>Finset.sum_nonneg fun c _=>hw c _)
    _ ≤ ∑x:Outsides R M G U,∑c,w c x := by
      simp only [Fintype.sum_sum_type]
      have h1 : 0≤∑r:R×Bool,∑c,w c (.inl r) := Finset.sum_nonneg fun r _=>Finset.sum_nonneg fun c _=>hw c _
      have h2 : 0≤∑m:M,∑c,w c (.inr (.inl m)) := Finset.sum_nonneg fun m _=>Finset.sum_nonneg fun c _=>hw c _
      have h3 : 0≤∑g:G,∑c,w c (.inr (.inr (.inl g))) := Finset.sum_nonneg fun g _=>Finset.sum_nonneg fun c _=>hw c _
      simp only [Fintype.sum_sum_type] at h1 h2 h3
      linarith
    _ = ∑c,∑x,w c x := Finset.sum_comm
    _ ≤ ∑_:Centers G M P I J,(1:ℝ) := Finset.sum_le_sum fun c _=>hrow c
    _ = _ := by simp

lemma significant_card_eq (w : Centers G M P I J→Outsides R M G U→ℝ) :
    (significant w).card=2*Fintype.card R+Fintype.card M+Fintype.card G+(highLeaves w).card := by
  have he : (highLeaves w).card=∑u:U,if 1<∑c,w c (.inr (.inr (.inr u))) then 1 else 0 := by
    rw [highLeaves,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [he]
  unfold significant
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [Fintype.sum_sum_type,lowUnmatched,
    not_false_eq_true,ite_true,not_le,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,Fintype.card_prod,Fintype.card_bool]
  norm_cast
  ring

lemma significant_card_le
    (w : Centers G M P I J→Outsides R M G U→ℝ)
    (hw : ∀c x,0≤w c x) (hrow : ∀c,∑x,w c x≤1)
    {μ : ℝ} (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hpairs : (Fintype.card R:ℝ)+(Fintype.card M:ℝ)+(Fintype.card G:ℝ)≤μ) :
    ((significant w).card:ℝ)≤3*μ := by
  rw [significant_card_eq]
  push_cast
  have h := highLeaves_card_le w hw hrow
  nlinarith [Nat.cast_nonneg (Fintype.card M) (α:=ℝ),Nat.cast_nonneg (Fintype.card G) (α:=ℝ)]

def centerError (ε : ℝ) (_layer : Bool) (_c : Centers G M P I J) : ℝ := ε

def outsideError (w : Centers G M P I J→Outsides R M G U→ℝ)
    (ε : ℝ) (_layer : Bool) (x : Outsides R M G U) : ℝ :=
  if lowUnmatched w x then 0 else 300*ε

lemma outsideError_nonneg (w : Centers G M P I J→Outsides R M G U→ℝ)
    {ε : ℝ} (hε : 0≤ε) (layer : Bool) (x : Outsides R M G U) :
    0≤outsideError w ε layer x := by unfold outsideError;split_ifs <;> positivity

lemma local_error_sum_le
    (w : Centers G M P I J→Outsides R M G U→ℝ)
    (hw : ∀c x,0≤w c x) (hrow : ∀c,∑x,w c x≤1)
    {μ ε : ℝ} (hε : 0≤ε)
    (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hpairs : (Fintype.card R:ℝ)+(Fintype.card M:ℝ)+(Fintype.card G:ℝ)≤μ) :
    (∑layer:Bool,∑c:Centers G M P I J,centerError ε layer c)+
      (∑layer:Bool,∑x,outsideError w ε layer x)≤2000*ε*μ := by
  have hs := significant_card_le w hw hrow hcenters hpairs
  have he (layer : Bool) : (∑x,outsideError w ε layer x)=((significant w).card:ℝ)*(300*ε) := by
    rw [show (∑x,outsideError w ε layer x)=∑x∈significant w,300*ε by
      simp only [outsideError,significant,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h:lowUnmatched w x <;> simp [h]]
    simp
  simp only [Fintype.sum_bool,he,centerError,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_bool,Nat.cast_ofNat]
  have hμ : 0≤μ := (Nat.cast_nonneg _).trans hcenters
  nlinarith [mul_nonneg hε hμ]

end RobustMatching.R8RepairProbability
