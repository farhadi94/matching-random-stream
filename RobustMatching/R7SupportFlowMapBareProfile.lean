import RobustMatching.R7SupportFlowMapRefunds
import RobustMatching.R7ClosedRepairTypedLabelingCounts
import RobustMatching.R7ClosedRepairTypedProfile

noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate

def vertexBareCredit {q} (data : ProfileData q) : Column q → ℝ
  | .center c => centerCredit data c.2
  | _ => 0
def vertexOutsideCredit {q} (data : ProfileData q) : Column q → ℝ
  | .outside x => outsideCredit data x
  | _ => 0

theorem vertex_phase_split {q} (data : ProfileData q) (k : Column q)
    (h : IsVertexColumn k) :
    (coeffLe data .phase k : ℝ)=vertexBareCredit data k+vertexOutsideCredit data k := by
  cases k <;> simp [IsVertexColumn] at h <;>
    simp [coeffLe,leTerms,coeff,vertexBareCredit,vertexOutsideCredit]

def kindBare {q} (data : ProfileData q) : PairKind → ℝ
  | .gate => (1+(data.alpha : ℝ))/2
  | .root | .missing | .internalMissing => (1-(data.omega : ℝ))/2
  | .internalAvailable => 1/2

theorem benchmark_bare_balance {q} (data : ProfileData q) (k : PairKind)
    (b0 b1 : Fin q) (m0 m1 : Fin 4) :
    vertexBareCredit data (leftColumn k b0 m0)+vertexBareCredit data (rightColumn k b1 m1)+
      pairWeight k*(coeffLe data .phase (pairColumn k b0 b1 m0 m1) : ℝ)=kindBare data k := by
  cases k <;>
    simp [vertexBareCredit,leftColumn,rightColumn,centerCredit,pairWeight,pairColumn,
      orderedRoot,orderedPair,coeffLe,leTerms,coeff,kindBare] <;>
    split_ifs <;> simp [coeff] <;> push_cast <;> ring

section Coordinates
variable {B U E : Type*} [Fintype B] [Fintype U] [Fintype E]
  [DecidableEq B] [DecidableEq U] {q : ℕ}

theorem coordinate_bare_profile (d : Coordinates B U q) (data : ProfileData q) :
    (∑ v, vertexBareCredit data (vertexColumn d v))+
      (∑ i, pairWeight (d.kind i)*(coeffLe data .phase (benchmarkColumn d i) : ℝ)) =
      ((1+(data.alpha : ℝ))*kindCount d .gate+
        (1-(data.omega : ℝ))*(kindCount d .missing+kindCount d .root+kindCount d .internalMissing)+
        kindCount d .internalAvailable)/2 := by
  have hu : (∑ u : U, vertexBareCredit data (vertexColumn d (.inr u)))=0 := by
    apply Finset.sum_eq_zero
    intro u _
    cases hu : d.unmatchedCenter u <;>
      simp [vertexColumn,hu,vertexBareCredit,centerCredit]
  rw [Fintype.sum_sum_type,hu,add_zero,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,vertexColumn,ite_true,show ¬((1 : Fin 2)=0) from by decide,ite_false]
  rw [←Finset.sum_add_distrib]
  have hp : (∑ i, (
      vertexBareCredit data (leftColumn (d.kind i) (d.bin (.inl (i,0))) (d.mask (.inl (i,0))))+
      vertexBareCredit data (rightColumn (d.kind i) (d.bin (.inl (i,1))) (d.mask (.inl (i,1))))+
      pairWeight (d.kind i)*(coeffLe data .phase (benchmarkColumn d i) : ℝ))) =
      ∑ i, kindBare data (d.kind i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact benchmark_bare_balance data _ _ _ _ _
  rw [hp]
  have hf (i : B) : kindBare data (d.kind i) =
      ((1+(data.alpha : ℝ))*(if d.kind i=.gate then 1 else 0)+
        (1-(data.omega : ℝ))*((if d.kind i=.missing then 1 else 0)+
          (if d.kind i=.root then 1 else 0)+(if d.kind i=.internalMissing then 1 else 0))+
        (if d.kind i=.internalAvailable then 1 else 0))/2 := by
    cases hk : d.kind i <;> simp [hk,kindBare]
  simp_rw [hf]
  unfold kindCount
  simp only [Finset.sum_div,Finset.sum_add_distrib,Finset.mul_sum,mul_add]
  rw [←Finset.sum_div]
  simp only [Finset.sum_add_distrib]

theorem rawProfile_split (d : Coordinates B U q) (ref : E → Column q)
    (data : ProfileData q) (beta : ℝ) :
    rawProfile d ref data beta =
      ((1+(data.alpha : ℝ))*kindCount d .gate+
        (1-(data.omega : ℝ))*(kindCount d .missing+kindCount d .root+kindCount d .internalMissing)+
        kindCount d .internalAvailable)/2+
      (∑ v, vertexOutsideCredit data (vertexColumn d v))+
      (∑ e, (coeffLe data .phase (ref e) : ℝ))/beta := by
  unfold rawProfile
  simp_rw [vertex_phase_split data _ (vertexColumn_is_vertex d _)]
  rw [Finset.sum_add_distrib]
  have h := coordinate_bare_profile d data
  linarith

end Coordinates
end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.coordinate_bare_profile
#print axioms RobustMatching.R7SupportFlowMap.rawProfile_split
