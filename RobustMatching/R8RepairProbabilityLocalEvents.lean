import RobustMatching.R8RepairProbabilityLocalHP
import RobustMatching.R8RepairProbabilityErrors

noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RobustMatching.R8RepairProbability
open R7ClosedRepair R7ClosedRepair.Typed
variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]

/-- The fixed graph data and deterministic original-copy fiber bounds.
There is no probabilistic event or concentration hypothesis in this record. -/
structure LocalData where
  parents : Parents B G M J R
  fallback : B
  H : Centers G M P I J→Outsides R M G U→Prop
  sideC : Centers G M P I J→Bool
  sideO : Outsides R M G U→Bool
  w : Centers G M P I J→Outsides R M G U→ℝ
  d : Outsides R M G U→ℝ
  beta : ℝ
  kappa : ℕ
  beta_pos : 0<beta
  kappa_pos : 0<kappa
  nonneg : ∀c x,0≤w c x
  crossing : ∀c x,H c x→sideC c≠sideO x
  supported : ∀c x,¬H c x→w c x=0
  row_capacity : ∀c,∑x,w c x≤1
  denominator : ∀x,(1:ℝ)/100≤d x
  edge_weight : ∀c x,w c x≤1/(beta*d x)
  column_mass : ∀x,∑c,w c x≤1/d x
  row_fibers : ∀layer c b,(Finset.univ.filter fun x=>H c x ∧
    outsideParent parents fallback x=b ∧ signalRange (receiverSignalAt sideO layer x)≠0).card≤2*kappa
  column_fibers : ∀layer x b,(Finset.univ.filter fun c=>H c x ∧
    centerParent parents fallback c=b ∧ signalRange (senderSignalAt sideO layer x c)≠0).card≤2*kappa

namespace LocalData

variable (D : LocalData (B:=B) (G:=G) (M:=M) (P:=P) (I:=I) (J:=J) (R:=R) (U:=U))

abbrev LocalIndex := (Bool×Centers G M P I J) ⊕
  (Bool×{x : Outsides R M G U // x∈significant D.w})

def localBad (ε : ℝ) : D.LocalIndex→Set (B→Clock)
  | .inl (layer,c) => {z | 1+ε<rowLoad
      (rawSupport (states D.parents z) D.H D.sideC D.sideO D.w
        (normalizer alpha omega D.sideO) layer) c}
  | .inr (layer,x) => {z | liveReceiver (states D.parents z) D.sideO layer x.1 ∧
      colLoad (rawSupport (states D.parents z) D.H D.sideC D.sideO D.w
        (normalizer alpha omega D.sideO) layer) x.1 <
          meanLoad alpha omega D.w D.sideO layer x.1/capacity alpha omega D.sideO layer x.1-300*ε}

lemma edge_cap (c : Centers G M P I J) (x : Outsides R M G U) : D.w c x≤100/D.beta := by
  have hd : 0<D.d x := by linarith [D.denominator x]
  refine (D.edge_weight c x).trans ?_
  apply (div_le_div_iff₀ (mul_pos D.beta_pos hd) D.beta_pos).mpr
  nlinarith [D.denominator x,D.beta_pos]

theorem localBad_measure {ε : ℝ} (hε : 0<ε) (i : D.LocalIndex) :
    (experiment (B:=B)).real (D.localBad ε i)≤Real.exp (-ε^2*D.beta/(4000*D.kappa)) := by
  rcases i with ⟨layer,c⟩|⟨layer,x⟩
  · exact row_failure_bound D.parents D.fallback D.H D.sideC D.sideO D.crossing
      D.w D.nonneg D.supported D.row_capacity layer c D.beta_pos hε D.edge_cap
      D.kappa D.kappa_pos (D.row_fibers layer c)
  · exact column_failure_bound D.parents D.fallback D.H D.sideC D.sideO D.crossing
      D.w D.nonneg D.supported layer x.1 D.beta_pos (D.denominator x.1) hε
      (fun c=>D.edge_weight c x.1) (D.column_mass x.1) D.kappa D.kappa_pos (D.column_fibers layer x.1)

theorem local_failure_union {ε μ : ℝ} (hε : 0<ε)
    (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hpairs : (Fintype.card R:ℝ)+(Fintype.card M:ℝ)+(Fintype.card G:ℝ)≤μ) :
    (experiment (B:=B)).real (⋃i,D.localBad ε i)≤8*μ*Real.exp (-ε^2*D.beta/(4000*D.kappa)) := by
  have h := bad_union_bound (D.localBad ε) (fun _=>Real.exp (-ε^2*D.beta/(4000*D.kappa)))
    (D.localBad_measure hε)
  have hs := significant_card_le D.w D.nonneg D.row_capacity hcenters hpairs
  have hc : (Fintype.card D.LocalIndex:ℝ)≤8*μ := by
    simp only [LocalIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_coe]
    push_cast
    simp only [Centers,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool] at hcenters
    push_cast at hcenters
    linarith
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right hc (le_of_lt (Real.exp_pos _)))

lemma local_events_imply_loads {ε : ℝ} (hε : 0≤ε) (z : B→Clock)
    (hz : z∉⋃i,D.localBad ε i) :
    (∀layer c,rowLoad (rawSupport (states D.parents z) D.H D.sideC D.sideO D.w
      (normalizer alpha omega D.sideO) layer) c≤1+centerError ε layer c) ∧
    (∀layer x,¬lowUnmatched D.w x→liveReceiver (states D.parents z) D.sideO layer x→
      meanLoad alpha omega D.w D.sideO layer x/capacity alpha omega D.sideO layer x-outsideError D.w ε layer x≤
        colLoad (rawSupport (states D.parents z) D.H D.sideC D.sideO D.w
          (normalizer alpha omega D.sideO) layer) x) := by
  have hn (i : D.LocalIndex) : z∉D.localBad ε i := fun hh=>hz (Set.mem_iUnion.mpr ⟨i,hh⟩)
  constructor
  · intro layer c
    exact le_of_not_gt (hn (.inl (layer,c)))
  · intro layer x hsig hlive
    have hx : x∈significant D.w := Finset.mem_filter.mpr ⟨Finset.mem_univ x,hsig⟩
    have hh := hn (.inr (layer,⟨x,hx⟩))
    have he : outsideError D.w ε layer x=300*ε := if_neg hsig
    rw [he]
    apply le_of_not_gt
    intro hlt
    exact hh ⟨hlive,hlt⟩

end LocalData
end RobustMatching.R8RepairProbability
