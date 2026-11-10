import RandomOrderMatching.Analysis.Repair.Probability.LocalEvents
import RandomOrderMatching.Analysis.Repair.Probability.CountTails
import RandomOrderMatching.Analysis.Repair.Probability.ParentFibers

noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair.Probability
open RandomOrderMatching.Analysis.Repair RandomOrderMatching.Analysis.Repair.Typed
variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]
namespace LocalData
variable (D : LocalData (B:=B) (G:=G) (M:=M) (P:=P) (I:=I) (J:=J) (R:=R) (U:=U))

def aggregateBad (t : ℝ) : Fin 5→Set (B→Clock) :=
  ![{z | (∑g,if (states D.parents z).active g=true then (1:ℝ) else 0)<alpha*(Fintype.card G:ℝ)-t},
    {z | (∑r,if (states D.parents z).earlyR r=false then (1:ℝ) else 0)<(1-omega)*(Fintype.card R:ℝ)-t},
    {z | (∑m,if (states D.parents z).earlyM m=false then (1:ℝ) else 0)<(1-omega)*(Fintype.card M:ℝ)-t},
    {z | (∑j,if (states D.parents z).earlyJ j=false then (1:ℝ) else 0)<(1-omega)*(Fintype.card J:ℝ)-t},
    {z | (∑layer:Bool,∑x,mixedValue (states D.parents z) alpha omega D.H D.sideC D.sideO D.w layer x)
      <outsideProfile alpha omega D.w-2*t}]

lemma random_counts_le {μ : ℝ} (hcount : randomPairCount G M J R≤μ) :
    (Fintype.card G:ℝ)≤μ ∧ (Fintype.card M:ℝ)≤μ ∧
      (Fintype.card J:ℝ)≤μ ∧ (Fintype.card R:ℝ)≤μ := by
  unfold randomPairCount at hcount
  have hg : (0:ℝ)≤Fintype.card G := Nat.cast_nonneg _
  have hm : (0:ℝ)≤Fintype.card M := Nat.cast_nonneg _
  have hj : (0:ℝ)≤Fintype.card J := Nat.cast_nonneg _
  have hr : (0:ℝ)≤Fintype.card R := Nat.cast_nonneg _
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma aggregateBad_measure {μ t : ℝ}
    (hblock : ∀b,originalMultiplicity D.parents b≤D.kappa)
    (hcount : randomPairCount G M J R≤μ) (hμ : 0<μ) (ht : 0<t) (i : Fin 5) :
    (experiment (B:=B)).real (D.aggregateBad t i)≤Real.exp (-2*t^2/((D.kappa:ℝ)*μ)) := by
  have hc := random_counts_le hcount
  have hk : (0:ℝ)<D.kappa := Nat.cast_pos.mpr D.kappa_pos
  have hf := pair_fibers_le D.parents D.kappa hblock
  fin_cases i
  · simpa only [aggregateBad,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,activeCount_eq,signalMean] using
      count_lower_tail D.parents.gate .active D.kappa (fun b=>(hf b).1)
        D.kappa_pos hμ hc.1 ht
  · simpa only [aggregateBad,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,lateRootCount_eq,signalMean] using
      count_lower_tail D.parents.root .late D.kappa (fun b=>(hf b).2.2.2)
        D.kappa_pos hμ hc.2.2.2 ht
  · simpa only [aggregateBad,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,lateMissingCount_eq,signalMean] using
      count_lower_tail D.parents.missing .late D.kappa (fun b=>(hf b).2.1)
        D.kappa_pos hμ hc.2.1 ht
  · simpa only [aggregateBad,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,lateInternalCount_eq,signalMean] using
      count_lower_tail D.parents.internalMissing .late D.kappa (fun b=>(hf b).2.2.1)
        D.kappa_pos hμ hc.2.2.1 ht
  · have hh := actual_mixed_lower_tail D.parents D.fallback D.H D.sideC D.sideO D.crossing
      D.w D.supported D.nonneg D.row_capacity (Nat.cast_nonneg D.kappa) hblock hcount
      (by positivity : (0:ℝ)<4*(D.kappa:ℝ)*μ) (by linarith : 0<2*t)
    have he : -2*(2*t)^2/(4*(D.kappa:ℝ)*μ)= -2*t^2/((D.kappa:ℝ)*μ) := by ring
    rw [he] at hh
    refine (measureReal_mono ?_).trans hh
    intro z hz
    change (∑layer:Bool,∑x,mixedValue (states D.parents z) alpha omega D.H D.sideC D.sideO D.w layer x)
      <outsideProfile alpha omega D.w-2*t at hz
    change 2*t≤outsideProfile alpha omega D.w-_
    linarith

theorem aggregate_failure_union {μ t : ℝ}
    (hblock : ∀b,originalMultiplicity D.parents b≤D.kappa)
    (hcount : randomPairCount G M J R≤μ) (hμ : 0<μ) (ht : 0<t) :
    (experiment (B:=B)).real (⋃i,D.aggregateBad t i)≤5*Real.exp (-2*t^2/((D.kappa:ℝ)*μ)) := by
  have h := bad_union_bound (D.aggregateBad t) (fun _=>Real.exp (-2*t^2/((D.kappa:ℝ)*μ)))
    (D.aggregateBad_measure hblock hcount hμ ht)
  simpa using h

lemma aggregate_events_imply_counts (t : ℝ) (z : B→Clock)
    (hz : z∉⋃i,D.aggregateBad t i) :
    (alpha*(Fintype.card G:ℝ)-t≤∑g,if (states D.parents z).active g=true then (1:ℝ) else 0) ∧
    ((1-omega)*(Fintype.card R:ℝ)-t≤∑r,if (states D.parents z).earlyR r=false then (1:ℝ) else 0) ∧
    ((1-omega)*(Fintype.card M:ℝ)-t≤∑m,if (states D.parents z).earlyM m=false then (1:ℝ) else 0) ∧
    ((1-omega)*(Fintype.card J:ℝ)-t≤∑j,if (states D.parents z).earlyJ j=false then (1:ℝ) else 0) ∧
    (outsideProfile alpha omega D.w-2*t≤∑layer:Bool,∑x,
      mixedValue (states D.parents z) alpha omega D.H D.sideC D.sideO D.w layer x) := by
  have hn (i : Fin 5) : z∉D.aggregateBad t i := fun hh=>hz (Set.mem_iUnion.mpr ⟨i,hh⟩)
  exact ⟨le_of_not_gt (hn 0),le_of_not_gt (hn 1),le_of_not_gt (hn 2),le_of_not_gt (hn 3),le_of_not_gt (hn 4)⟩

end LocalData
end RandomOrderMatching.Analysis.Repair.Probability
