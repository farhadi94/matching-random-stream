import RobustMatching.R7SupportFlowMapIncidence
import RobustMatching.R7SupportFlowMapFromGraph

/-! Degree rows of the concrete graph primal, derived from local endpoint
incidences and local bin bounds. No matrix degree inequality is assumed. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate

def IsDegreeRow {q} : LeRow q → Prop
  | .centerLower _ | .centerUpper _ | .outsideLower _ | .outsideUpper _ => True
  | _ => False

theorem benchmark_degree_zero {q} (data : ProfileData q) (k : PairKind)
    (b0 b1 : Fin q) (m0 m1 : Fin 4) (r : LeRow q) (hr : IsDegreeRow r) :
    coeffLe data r (pairColumn k b0 b1 m0 m1)=0 := by
  cases r <;> simp [IsDegreeRow] at hr <;>
    cases k <;> simp [pairColumn,orderedRoot,orderedPair,coeffLe,leTerms,coeff] <;>
    split_ifs <;> simp [coeff]

theorem vertex_center_lower {q} (data : ProfileData q) (v : Column q)
    (hv : IsVertexColumn v) (c : CenterClass q) :
    (coeffLe data (.centerLower c) v : ℝ) =
      (lower data c.1 : ℝ)*(if v=.center c then 1 else 0) := by
  cases v <;> simp [IsVertexColumn] at hv
  · rename_i a
    by_cases ha : a=c
    · subst a; simp [coeffLe,leTerms,coeff]
    · simp [coeffLe,leTerms,coeff,ha]
  · simp [coeffLe,leTerms,coeff]

theorem vertex_center_upper {q} (data : ProfileData q) (v : Column q)
    (hv : IsVertexColumn v) (c : CenterClass q) :
    (coeffLe data (.centerUpper c) v : ℝ) =
      -(upper data c.1 : ℝ)*(if v=.center c then 1 else 0) := by
  cases v <;> simp [IsVertexColumn] at hv
  · rename_i a
    by_cases ha : a=c
    · subst a; simp [coeffLe,leTerms,coeff]
    · simp [coeffLe,leTerms,coeff,ha]
  · simp [coeffLe,leTerms,coeff]

theorem vertex_outside_lower {q} (data : ProfileData q) (v : Column q)
    (hv : IsVertexColumn v) (x : OutsideClass q) :
    (coeffLe data (.outsideLower x) v : ℝ) =
      (lower data x.1 : ℝ)*(if v=.outside x then 1 else 0) := by
  cases v <;> simp [IsVertexColumn] at hv
  · simp [coeffLe,leTerms,coeff]
  · rename_i y
    by_cases hy : y=x
    · subst y; simp [coeffLe,leTerms,coeff]
    · simp [coeffLe,leTerms,coeff,hy]

theorem vertex_outside_upper {q} (data : ProfileData q) (v : Column q)
    (hv : IsVertexColumn v) (x : OutsideClass q) :
    (coeffLe data (.outsideUpper x) v : ℝ) =
      -(upper data x.1 : ℝ)*(if v=.outside x then 1 else 0) := by
  cases v <;> simp [IsVertexColumn] at hv
  · simp [coeffLe,leTerms,coeff]
  · rename_i y
    by_cases hy : y=x
    · subst y; simp [coeffLe,leTerms,coeff]
    · simp [coeffLe,leTerms,coeff,hy]

theorem class_degree_lower {V K : Type*} [Fintype V] [DecidableEq K]
    (tag : V → K) (degree : V → ℝ) (k : K) (beta bound : ℝ)
    (h : ∀ v, tag v=k → beta*bound ≤ degree v) :
    beta*bound*pushMass Finset.univ tag (fun _ => 1) k ≤
      pushMass Finset.univ tag degree k := by
  simp only [pushMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : tag v=k
  · simpa [hv] using h v hv
  · simp [hv]

theorem class_degree_upper {V K : Type*} [Fintype V] [DecidableEq K]
    (tag : V → K) (degree : V → ℝ) (k : K) (beta bound : ℝ)
    (h : ∀ v, tag v=k → degree v ≤ beta*bound) :
    pushMass Finset.univ tag degree k ≤
      beta*bound*pushMass Finset.univ tag (fun _ => 1) k := by
  simp only [pushMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : tag v=k
  · simpa [hv] using h v hv
  · simp [hv]

section PrimalRows
variable {B U E : Type*} [Fintype B] [Fintype U] [Fintype E]
  [DecidableEq B] [DecidableEq U] {q : ℕ}

theorem graphPrimal_degree_formula
    (d : Coordinates B U q) (ref : E → Column q)
    (l t : E → Vertex B U) (data : ProfileData q)
    (row : LeRow q) (key : Column q) (s bound beta value : ℝ)
    (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (hv : ∀ v, (coeffLe data row (vertexColumn d v) : ℝ) =
      s*bound*(if vertexColumn d v=key then 1 else 0))
    (hb : ∀ i, pairWeight (d.kind i)*(coeffLe data row (benchmarkColumn d i) : ℝ)=0)
    (hz : coeffLe data row .z=0) (hvalue : coeffLe data row .value=0)
    (href : ∀ e, (coeffLe data row (ref e) : ℝ) =
      -s*((if vertexColumn d (l e)=key then 1 else 0)+
          (if vertexColumn d (t e)=key then 1 else 0))) :
    (∑ c, (coeffLe data row c : ℝ)*graphPrimal d ref beta value c) =
      s*(bound*rawVertices d key-
        pushMass Finset.univ (vertexColumn d) (endpointDegree l t) key/beta) /
        (Fintype.card B : ℝ) := by
  have hvs : (∑ v, (coeffLe data row (vertexColumn d v) : ℝ)) =
      s*bound*rawVertices d key := by
    simp_rw [hv]
    simp only [rawVertices,pushMass,Finset.mul_sum]
  have hbs : (∑ i, pairWeight (d.kind i)*(coeffLe data row (benchmarkColumn d i) : ℝ))=0 :=
    Finset.sum_eq_zero fun i _ => hb i
  have hrs : (∑ e, (coeffLe data row (ref e) : ℝ)) =
      -s*pushMass Finset.univ (vertexColumn d) (endpointDegree l t) key := by
    rw [endpointDegree_class_sum,Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => href e
  rw [graphPrimal_eval,hvs,hbs,hz,hvalue,hrs]
  push_cast
  field_simp [ne_of_gt hbeta,ne_of_gt hmu]
  ring

theorem degree_lower_expression_nonpos {count degree beta bound mu : ℝ}
    (hbeta : 0 < beta) (hmu : 0 < mu)
    (h : beta*bound*count ≤ degree) :
    (bound*count-degree/beta)/mu ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ hmu.le
  apply sub_nonpos.mpr
  apply (le_div_iff₀ hbeta).2
  nlinarith

theorem degree_upper_expression_nonpos {count degree beta bound mu : ℝ}
    (hbeta : 0 < beta) (hmu : 0 < mu)
    (h : degree ≤ beta*bound*count) :
    -(bound*count-degree/beta)/mu ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ hmu.le
  have hh : degree/beta ≤ bound*count := (div_le_iff₀ hbeta).2 (by nlinarith)
  linarith

theorem coordinate_benchmark_degree_zero
    (d : Coordinates B U q) (data : ProfileData q)
    (row : LeRow q) (hr : IsDegreeRow row) (i : B) :
    coeffLe data row (benchmarkColumn d i)=0 :=
  benchmark_degree_zero data (d.kind i) _ _ _ _ row hr

theorem graphPrimal_centerLower
    (d : Coordinates B U q) (ref : E → Column q)
    (l t : E → Vertex B U) (data : ProfileData q)
    (hRef : ∀ e, ReferenceCompatible (vertexColumn d (l e))
      (vertexColumn d (t e)) (ref e))
    (beta value : ℝ) (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (c : CenterClass q)
    (hbin : ∀ v, vertexColumn d v=.center c → beta*(lower data c.1 : ℝ) ≤ endpointDegree l t v) :
    (∑ k, (coeffLe data (.centerLower c) k : ℝ)*graphPrimal d ref beta value k) ≤ 0 := by
  have hf := graphPrimal_degree_formula d ref l t data (.centerLower c) (.center c)
    1 (lower data c.1 : ℝ) beta value hbeta hmu
    (fun v => by simpa using vertex_center_lower data _ (vertexColumn_is_vertex d v) c)
    (fun i => by rw [coordinate_benchmark_degree_zero d data _ (by trivial)]; norm_num)
    (by simp [coeffLe,leTerms,coeff]) (by simp [coeffLe,leTerms,coeff])
    (fun e => by rw [reference_center_lower data _ _ _ (hRef e) c]; ring)
  rw [hf]
  simp only [one_mul,neg_one_mul]
  exact degree_lower_expression_nonpos hbeta hmu
    (class_degree_lower (vertexColumn d) (endpointDegree l t) (.center c) beta (lower data c.1 : ℝ) hbin)

theorem graphPrimal_centerUpper
    (d : Coordinates B U q) (ref : E → Column q)
    (l t : E → Vertex B U) (data : ProfileData q)
    (hRef : ∀ e, ReferenceCompatible (vertexColumn d (l e))
      (vertexColumn d (t e)) (ref e))
    (beta value : ℝ) (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (c : CenterClass q)
    (hbin : ∀ v, vertexColumn d v=.center c → endpointDegree l t v ≤ beta*(upper data c.1 : ℝ)) :
    (∑ k, (coeffLe data (.centerUpper c) k : ℝ)*graphPrimal d ref beta value k) ≤ 0 := by
  have hf := graphPrimal_degree_formula d ref l t data (.centerUpper c) (.center c)
    (-1) (upper data c.1 : ℝ) beta value hbeta hmu
    (fun v => by simpa using vertex_center_upper data _ (vertexColumn_is_vertex d v) c)
    (fun i => by rw [coordinate_benchmark_degree_zero d data _ (by trivial)]; norm_num)
    (by simp [coeffLe,leTerms,coeff]) (by simp [coeffLe,leTerms,coeff])
    (fun e => by rw [reference_center_upper data _ _ _ (hRef e) c]; ring)
  rw [hf]
  simp only [one_mul,neg_one_mul]
  exact degree_upper_expression_nonpos hbeta hmu
    (class_degree_upper (vertexColumn d) (endpointDegree l t) (.center c) beta (upper data c.1 : ℝ) hbin)

theorem graphPrimal_outsideLower
    (d : Coordinates B U q) (ref : E → Column q)
    (l t : E → Vertex B U) (data : ProfileData q)
    (hRef : ∀ e, ReferenceCompatible (vertexColumn d (l e))
      (vertexColumn d (t e)) (ref e))
    (beta value : ℝ) (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (x : OutsideClass q)
    (hbin : ∀ v, vertexColumn d v=.outside x → beta*(lower data x.1 : ℝ) ≤ endpointDegree l t v) :
    (∑ k, (coeffLe data (.outsideLower x) k : ℝ)*graphPrimal d ref beta value k) ≤ 0 := by
  have hf := graphPrimal_degree_formula d ref l t data (.outsideLower x) (.outside x)
    1 (lower data x.1 : ℝ) beta value hbeta hmu
    (fun v => by simpa using vertex_outside_lower data _ (vertexColumn_is_vertex d v) x)
    (fun i => by rw [coordinate_benchmark_degree_zero d data _ (by trivial)]; norm_num)
    (by simp [coeffLe,leTerms,coeff]) (by simp [coeffLe,leTerms,coeff])
    (fun e => by rw [reference_outside_lower data _ _ _ (hRef e) x]; ring)
  rw [hf]
  simp only [one_mul,neg_one_mul]
  exact degree_lower_expression_nonpos hbeta hmu
    (class_degree_lower (vertexColumn d) (endpointDegree l t) (.outside x) beta (lower data x.1 : ℝ) hbin)

theorem graphPrimal_outsideUpper
    (d : Coordinates B U q) (ref : E → Column q)
    (l t : E → Vertex B U) (data : ProfileData q)
    (hRef : ∀ e, ReferenceCompatible (vertexColumn d (l e))
      (vertexColumn d (t e)) (ref e))
    (beta value : ℝ) (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (x : OutsideClass q)
    (hbin : ∀ v, vertexColumn d v=.outside x → endpointDegree l t v ≤ beta*(upper data x.1 : ℝ)) :
    (∑ k, (coeffLe data (.outsideUpper x) k : ℝ)*graphPrimal d ref beta value k) ≤ 0 := by
  have hf := graphPrimal_degree_formula d ref l t data (.outsideUpper x) (.outside x)
    (-1) (upper data x.1 : ℝ) beta value hbeta hmu
    (fun v => by simpa using vertex_outside_upper data _ (vertexColumn_is_vertex d v) x)
    (fun i => by rw [coordinate_benchmark_degree_zero d data _ (by trivial)]; norm_num)
    (by simp [coeffLe,leTerms,coeff]) (by simp [coeffLe,leTerms,coeff])
    (fun e => by rw [reference_outside_upper data _ _ _ (hRef e) x]; ring)
  rw [hf]
  simp only [one_mul,neg_one_mul]
  exact degree_upper_expression_nonpos hbeta hmu
    (class_degree_upper (vertexColumn d) (endpointDegree l t) (.outside x) beta (upper data x.1 : ℝ) hbin)

end PrimalRows
end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_degree_formula
#print axioms RobustMatching.R7SupportFlowMap.class_degree_lower
#print axioms RobustMatching.R7SupportFlowMap.class_degree_upper

#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_centerLower
#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_centerUpper
#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_outsideLower
#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_outsideUpper
