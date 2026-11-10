import RobustMatching.R7SupportFlowMapDegreeRows

/-! The two aggregate degree moments are sums over actual benchmark pairs.
Reference incidences at both marked endpoints are counted separately. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate

def rootMark {q} : Column q → ℝ
  | .outside x => if x.2.1=.S then 1 else 0
  | _ => 0
def missingMark {q} : Column q → ℝ
  | .center c => if c.2=.M then 1 else 0
  | .outside x => if x.2.1=.T then 1 else 0
  | _ => 0

theorem reference_root_moment {q} (data : ProfileData q) (u v e : Column q)
    (h : ReferenceCompatible u v e) :
    (coeffLe data .rootMoment e : ℝ) = -(rootMark u+rootMark v) := by
  rcases h with ⟨a,b,rfl,rfl,hh | hh⟩ | ⟨a,x,rfl,rfl,rfl⟩ | ⟨a,x,rfl,rfl,rfl⟩ <;>
    try subst e
  all_goals simp [coeffLe,leTerms,coeff,rootMark] <;> split_ifs <;> norm_num

theorem reference_missing_moment {q} (data : ProfileData q) (u v e : Column q)
    (h : ReferenceCompatible u v e) :
    (coeffLe data .missingMoment e : ℝ) = -(missingMark u+missingMark v) := by
  rcases h with ⟨a,b,rfl,rfl,hh | hh⟩ | ⟨a,x,rfl,rfl,rfl⟩ | ⟨a,x,rfl,rfl,rfl⟩ <;>
    try subst e
  all_goals simp [coeffLe,leTerms,coeff,missingMark] <;> split_ifs <;> norm_num

theorem benchmark_root_moment {q} (data : ProfileData q) (k : PairKind)
    (b0 b1 : Fin q) (m0 m1 : Fin 4) :
    pairWeight k*(coeffLe data .rootMoment (pairColumn k b0 b1 m0 m1) : ℝ) =
      (1-(data.lam : ℝ))*(if k=.root then 1 else 0) := by
  cases k <;> simp [pairColumn,pairWeight,orderedRoot,orderedPair,coeffLe,leTerms,coeff] <;>
    split_ifs <;> simp [coeff]

theorem benchmark_missing_moment {q} (data : ProfileData q) (k : PairKind)
    (b0 b1 : Fin q) (m0 m1 : Fin 4) :
    pairWeight k*(coeffLe data .missingMoment (pairColumn k b0 b1 m0 m1) : ℝ) =
      (1-(data.lam : ℝ))*(if k=.missing then 1 else 0) := by
  cases k <;> simp [pairColumn,pairWeight,orderedRoot,orderedPair,coeffLe,leTerms,coeff] <;>
    split_ifs <;> simp [coeff]

theorem vertex_moments_zero {q} (data : ProfileData q) (v : Column q)
    (hv : IsVertexColumn v) : coeffLe data .rootMoment v=0 ∧ coeffLe data .missingMoment v=0 := by
  cases v <;> simp [IsVertexColumn] at hv <;> simp [coeffLe,leTerms,coeff]

section Coordinates
variable {B U E : Type*} [Fintype B] [Fintype U] [Fintype E]
  [DecidableEq B] [DecidableEq U] {q : ℕ}

def kindCount (d : Coordinates B U q) (target : PairKind) : ℝ :=
  ∑ i, if d.kind i=target then 1 else 0

theorem coordinate_marker_sum (d : Coordinates B U q) (mark : Column q → ℝ)
    (target : PairKind) (degree : Vertex B U → ℝ)
    (hl : ∀ k b m, mark (leftColumn k b m)=(if k=target then 1 else 0))
    (hr : ∀ k b m, mark (rightColumn k b m)=(if k=target then 1 else 0))
    (hu : ∀ b m (c : Bool), mark (if c then .center (b,.P) else .outside (b,.O,m))=0) :
    (∑ v, mark (vertexColumn d v)*degree v) =
      ∑ i, (if d.kind i=target then 1 else 0)*
        (degree (.inl (i,0))+degree (.inl (i,1))) := by
  have hum : (∑ u : U, mark (vertexColumn d (.inr u))*degree (.inr u))=0 := by
    apply Finset.sum_eq_zero
    intro u _
    have hh := hu (d.bin (.inr u)) (d.mask (.inr u)) (d.unmatchedCenter u)
    change mark (if d.unmatchedCenter u then _ else _)*_=0
    rw [hh,zero_mul]
  rw [Fintype.sum_sum_type,hum,add_zero,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,vertexColumn]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
  rw [hl,hr]
  ring

theorem coordinate_moment_lower (d : Coordinates B U q) (mark : Column q → ℝ)
    (target : PairKind) (degree : Vertex B U → ℝ) (beta bound : ℝ)
    (hl : ∀ k b m, mark (leftColumn k b m)=(if k=target then 1 else 0))
    (hr : ∀ k b m, mark (rightColumn k b m)=(if k=target then 1 else 0))
    (hu : ∀ b m (c : Bool), mark (if c then .center (b,.P) else .outside (b,.O,m))=0)
    (hpair : ∀ i, d.kind i=target →
      beta*bound ≤ degree (.inl (i,0))+degree (.inl (i,1))) :
    beta*bound*kindCount d target ≤ ∑ v, mark (vertexColumn d v)*degree v := by
  rw [coordinate_marker_sum d mark target degree hl hr hu]
  unfold kindCount
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : d.kind i=target
  · simpa [hi] using hpair i hi
  · simp [hi]

theorem graphPrimal_moment_formula
    (d : Coordinates B U q) (ref : E → Column q) (l t : E → Vertex B U)
    (data : ProfileData q) (row : LeRow q) (target : PairKind) (mark : Column q → ℝ)
    (beta value : ℝ) (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (hv : ∀ v, coeffLe data row (vertexColumn d v)=0)
    (hb : ∀ i, pairWeight (d.kind i)*(coeffLe data row (benchmarkColumn d i) : ℝ) =
      (1-(data.lam : ℝ))*(if d.kind i=target then 1 else 0))
    (hz : coeffLe data row .z=0) (hvalue : coeffLe data row .value=0)
    (href : ∀ e, (coeffLe data row (ref e) : ℝ) =
      -(mark (vertexColumn d (l e))+mark (vertexColumn d (t e)))) :
    (∑ c, (coeffLe data row c : ℝ)*graphPrimal d ref beta value c) =
      ((1-(data.lam : ℝ))*kindCount d target-
        (∑ v, mark (vertexColumn d v)*endpointDegree l t v)/beta) /
        (Fintype.card B : ℝ) := by
  have hvs : (∑ v, (coeffLe data row (vertexColumn d v) : ℝ))=0 := by simp [hv]
  have hbs : (∑ i, pairWeight (d.kind i)*(coeffLe data row (benchmarkColumn d i) : ℝ)) =
      (1-(data.lam : ℝ))*kindCount d target := by
    simp_rw [hb]
    simp only [kindCount,Finset.mul_sum]
  have hrs : (∑ e, (coeffLe data row (ref e) : ℝ)) =
      -(∑ v, mark (vertexColumn d v)*endpointDegree l t v) := by
    rw [endpointDegree_sum,←Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun e _ => href e
  rw [graphPrimal_eval,hvs,hbs,hz,hvalue,hrs]
  push_cast
  field_simp [ne_of_gt hbeta,ne_of_gt hmu]
  ring

theorem graphPrimal_rootMoment
    (d : Coordinates B U q) (ref : E → Column q) (l t : E → Vertex B U)
    (data : ProfileData q)
    (hRef : ∀ e, ReferenceCompatible (vertexColumn d (l e)) (vertexColumn d (t e)) (ref e))
    (beta value : ℝ) (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (hpair : ∀ i, d.kind i=.root → beta*(1-(data.lam : ℝ)) ≤
      endpointDegree l t (.inl (i,0))+endpointDegree l t (.inl (i,1))) :
    (∑ c, (coeffLe data .rootMoment c : ℝ)*graphPrimal d ref beta value c) ≤ 0 := by
  have hb := coordinate_moment_lower d rootMark .root (endpointDegree l t)
    beta (1-(data.lam : ℝ))
    (by intro k b m; cases k <;> simp [leftColumn,rootMark])
    (by intro k b m; cases k <;> simp [rightColumn,rootMark])
    (by intro b m c; cases c <;> simp [rootMark]) hpair
  have hf := graphPrimal_moment_formula d ref l t data .rootMoment .root rootMark
    beta value hbeta hmu
    (fun v => (vertex_moments_zero data _ (vertexColumn_is_vertex d v)).1)
    (fun i => benchmark_root_moment data (d.kind i) _ _ _ _)
    (by simp [coeffLe,leTerms,coeff]) (by simp [coeffLe,leTerms,coeff])
    (fun e => reference_root_moment data _ _ _ (hRef e))
  rw [hf]
  exact degree_lower_expression_nonpos hbeta hmu hb

theorem graphPrimal_missingMoment
    (d : Coordinates B U q) (ref : E → Column q) (l t : E → Vertex B U)
    (data : ProfileData q)
    (hRef : ∀ e, ReferenceCompatible (vertexColumn d (l e)) (vertexColumn d (t e)) (ref e))
    (beta value : ℝ) (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (hpair : ∀ i, d.kind i=.missing → beta*(1-(data.lam : ℝ)) ≤
      endpointDegree l t (.inl (i,0))+endpointDegree l t (.inl (i,1))) :
    (∑ c, (coeffLe data .missingMoment c : ℝ)*graphPrimal d ref beta value c) ≤ 0 := by
  have hb := coordinate_moment_lower d missingMark .missing (endpointDegree l t)
    beta (1-(data.lam : ℝ))
    (by intro k b m; cases k <;> simp [leftColumn,missingMark])
    (by intro k b m; cases k <;> simp [rightColumn,missingMark])
    (by intro b m c; cases c <;> simp [missingMark]) hpair
  have hf := graphPrimal_moment_formula d ref l t data .missingMoment .missing missingMark
    beta value hbeta hmu
    (fun v => (vertex_moments_zero data _ (vertexColumn_is_vertex d v)).2)
    (fun i => benchmark_missing_moment data (d.kind i) _ _ _ _)
    (by simp [coeffLe,leTerms,coeff]) (by simp [coeffLe,leTerms,coeff])
    (fun e => reference_missing_moment data _ _ _ (hRef e))
  rw [hf]
  exact degree_lower_expression_nonpos hbeta hmu hb

end Coordinates
end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.coordinate_moment_lower
#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_moment_formula

#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_rootMoment
#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_missingMoment
