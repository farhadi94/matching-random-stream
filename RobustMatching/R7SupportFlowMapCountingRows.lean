import RobustMatching.R7SupportFlowMapMass
import RobustMatching.R7SupportFlowMapDegreeRows

/-! Count and objective rows for the actual graph primal. The exceptional
zero-bin unmatched column is omitted exactly, not charged to an error term. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate

def PositiveOutside {q} : Column q → Prop
  | .outside x => x.2.1=.O ∧ x.1.val ≠ 0
  | _ => False
instance {q} (k : Column q) : Decidable (PositiveOutside k) := by
  cases k <;> unfold PositiveOutside <;> infer_instance
def positiveMark {q} (k : Column q) : ℝ := if PositiveOutside k then 1 else 0

theorem centerMark_nonneg {q} (k : Column q) : 0 ≤ centerMark k := by
  unfold centerMark; split_ifs <;> norm_num
theorem positiveMark_nonneg {q} (k : Column q) : 0 ≤ positiveMark k := by
  unfold positiveMark; split_ifs <;> norm_num
theorem positiveOutside_not_center {q} (k : Column q) (h : PositiveOutside k) :
    ¬IsCenterColumn k := by cases k <;> simp [PositiveOutside,IsCenterColumn] at *

theorem vertex_mass_le_one {q} (data : ProfileData q) (k : Column q) (h : IsVertexColumn k) :
    (coeffLe data .mass k : ℝ) ≤ 1 := by
  cases k <;> simp [IsVertexColumn] at h <;>
    simp [coeffLe,leTerms,coeff] <;> split_ifs <;> norm_num

theorem unmatched_mass_identity {q} (data : ProfileData q) (b : Fin q) (m : Fin 4) (c : Bool) :
    (coeffLe data .mass (if c then .center (b,.P) else .outside (b,.O,m)) : ℝ) =
      centerMark (if c then .center (b,.P) else .outside (b,.O,m))+
      positiveMark (if c then .center (b,.P) else .outside (b,.O,m)) := by
  cases c <;> simp [coeffLe,leTerms,coeff,centerMark,IsCenterColumn,positiveMark,PositiveOutside] <;>
    split_ifs <;> norm_num

section Coordinates
variable {B U E : Type*} [Fintype B] [Fintype U] [Fintype E]
  [DecidableEq B] [DecidableEq U] {q : ℕ}

theorem vertex_mass_total (d : Coordinates B U q) (data : ProfileData q) :
    (∑ v, (coeffLe data .mass (vertexColumn d v) : ℝ)) ≤
      2*(Fintype.card B : ℝ)+centerCount (vertexColumn d)+
        (∑ v, positiveMark (vertexColumn d v)) := by
  have hp : ∀ v : Vertex B U,
      (coeffLe data .mass (vertexColumn d v) : ℝ) ≤
      (match v with | .inl _ => 1 | .inr _ => 0)+
      centerMark (vertexColumn d v)+positiveMark (vertexColumn d v) := by
    intro v
    cases v with
    | inl x =>
      have h1 := vertex_mass_le_one data _ (vertexColumn_is_vertex d (.inl x))
      have h2 := centerMark_nonneg (vertexColumn d (.inl x))
      have h3 := positiveMark_nonneg (vertexColumn d (.inl x))
      dsimp only
      linarith
    | inr u =>
      simpa only [zero_add,vertexColumn] using
        (unmatched_mass_identity data (d.bin (.inr u)) (d.mask (.inr u))
          (d.unmatchedCenter u)).le
  have hs := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Vertex B U))) => hp v)
  simpa [Finset.sum_add_distrib,centerCount,Fintype.sum_sum_type,mul_comm] using hs

theorem pairWeight_le_one (k : PairKind) : pairWeight k ≤ 1 := by cases k <;> norm_num [pairWeight]
theorem internalWeight_le_one (k : PairKind) : internalWeight k ≤ 1 := by cases k <;> norm_num [internalWeight]
theorem internalCount_le (d : Coordinates B U q) : internalCount d ≤ (Fintype.card B : ℝ) := by
  calc
    internalCount d ≤ ∑ _i : B, (1 : ℝ) := Finset.sum_le_sum fun i _ => internalWeight_le_one _
    _ = (Fintype.card B : ℝ) := by simp

theorem benchmark_mass_one (d : Coordinates B U q) (data : ProfileData q) (i : B) :
    coeffLe data .mass (benchmarkColumn d i)=1 := by
  cases hk : d.kind i <;>
    simp [benchmarkColumn,hk,pairColumn,orderedRoot,orderedPair,coeffLe,leTerms,coeff] <;>
    split_ifs <;> simp [coeff]

theorem reference_mass_one (data : ProfileData q) (c f : CenterClass q) (x : OutsideClass q) :
    coeffLe data .mass (.cross c x)=1 ∧ coeffLe data .mass (.internal c f)=1 := by
  simp [coeffLe,leTerms,coeff]

theorem positive_mark_count (d : Coordinates B U q) :
    (∑ v, positiveMark (vertexColumn d v)) =
      ((Finset.univ.filter fun v => PositiveOutside (vertexColumn d v)).card : ℝ) := by
  simp only [positiveMark,Finset.sum_boole]

theorem graphPrimal_mass
    (d : Coordinates B U q) (ref : E → Column q) (l r : E → Vertex B U)
    (data : ProfileData q)
    (hRef : ∀ e, ReferenceCompatible (vertexColumn d (l e)) (vertexColumn d (r e)) (ref e))
    (beta value : ℝ) (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (hvalue : value ≤ 1) (hb : centerCount (vertexColumn d) ≤ (Fintype.card B : ℝ))
    (hdegree : ∀ v, IsCenterColumn (vertexColumn d v) → endpointDegree l r v ≤ beta)
    (hpositive : ∀ v, PositiveOutside (vertexColumn d v) → beta/256 ≤ endpointDegree l r v)
    (hmass : 263 ≤ data.massBound) :
    (∑ c, (coeffLe data .mass c : ℝ)*graphPrimal d ref beta value c) ≤ data.massBound := by
  have hpos : (∑ v, positiveMark (vertexColumn d v)) ≤ 256*centerCount (vertexColumn d) := by
    rw [positive_mark_count]
    apply positive_outside_count (vertexColumn d) ref l r hRef _ beta hbeta hdegree
    · intro v hv
      exact positiveOutside_not_center _ (Finset.mem_filter.mp hv).2
    · intro v hv
      exact hpositive v (Finset.mem_filter.mp hv).2
  have hv := vertex_mass_total d data
  have hv' : (∑ v, (coeffLe data .mass (vertexColumn d v) : ℝ)) ≤
      259*(Fintype.card B : ℝ) := by linarith
  have hpair : (∑ i, pairWeight (d.kind i)*(coeffLe data .mass (benchmarkColumn d i) : ℝ)) ≤
      (Fintype.card B : ℝ) := by
    simp_rw [benchmark_mass_one]
    simp only [Rat.cast_one,mul_one]
    calc
      (∑ i, pairWeight (d.kind i)) ≤ ∑ _i : B, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => pairWeight_le_one _
      _ = (Fintype.card B : ℝ) := by simp
  have hz : internalCount d ≤ (Fintype.card B : ℝ) := internalCount_le d
  have href : (∑ e, (coeffLe data .mass (ref e) : ℝ)) = (Fintype.card E : ℝ) := by
    calc
      (∑ e, (coeffLe data .mass (ref e) : ℝ)) = ∑ _e : E, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro e _
        rcases hRef e with ⟨a,b,_,_,hh | hh⟩ | ⟨a,x,_,_,hh⟩ | ⟨a,x,_,_,hh⟩ <;>
          simp [hh,coeffLe,leTerms,coeff]
      _ = (Fintype.card E : ℝ) := by simp
  have hedge := reference_count_le_beta_centers (vertexColumn d) ref l r hRef beta hdegree
  have hedge' : (Fintype.card E : ℝ) ≤ beta*(Fintype.card B : ℝ) :=
    hedge.trans (mul_le_mul_of_nonneg_left hb hbeta.le)
  rw [graphPrimal_eval,href]
  have hzcoef : coeffLe data .mass (.z : Column q)=1 := by simp [coeffLe,leTerms,coeff]
  have hvcoef : coeffLe data .mass (.value : Column q)=1 := by simp [coeffLe,leTerms,coeff]
  rw [hzcoef,hvcoef]
  push_cast
  have hfirst : ((∑ v, (coeffLe data .mass (vertexColumn d v) : ℝ))+
      (∑ i, pairWeight (d.kind i)*(coeffLe data .mass (benchmarkColumn d i) : ℝ))+
      internalCount d)/(Fintype.card B : ℝ) ≤ 261 := by
    apply (div_le_iff₀ hmu).2
    linarith
  have hsecond : (Fintype.card E : ℝ)/(beta*(Fintype.card B : ℝ)) ≤ 1 :=
    (div_le_iff₀ (mul_pos hbeta hmu)).2 (by simpa using hedge')
  have hm : (263 : ℝ) ≤ data.massBound := by exact_mod_cast hmass
  simp only [mul_one,one_mul]
  linarith

end Coordinates
end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_mass
