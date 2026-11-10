import RobustMatching.R7SupportFlowMapObjectiveRows
import RobustMatching.R7SupportFlowMapMomentRows
import RobustMatching.R7ReductionCertificate

/-! The concrete certificate applied to the explicit pushforward of graph
vertices, reference incidences, and benchmark pairs. All matrix rows are
derived here from local graph bounds; row feasibility is not a premise. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate

section Graph
variable {B U E : Type*} [Fintype B] [Fintype U] [Fintype E]
  [DecidableEq B] [DecidableEq U] {q : ℕ}

structure ProfileGeometry (d : Coordinates B U q) (ref : E → Column q)
    (l r : E → Vertex B U) (data : ProfileData q) (beta : ℝ) : Prop where
  compatible : ∀ e, ReferenceCompatible (vertexColumn d (l e)) (vertexColumn d (r e)) (ref e)
  vertex_allowed : ∀ v, columnAllowed data (vertexColumn d v)
  benchmark_allowed : ∀ i, columnAllowed data (benchmarkColumn d i)
  reference_allowed : ∀ e, columnAllowed data (ref e)
  center_lower : ∀ c v, vertexColumn d v=.center c →
    beta*(lower data c.1 : ℝ) ≤ endpointDegree l r v
  center_upper : ∀ c v, vertexColumn d v=.center c →
    endpointDegree l r v ≤ beta*(upper data c.1 : ℝ)
  outside_lower : ∀ x v, vertexColumn d v=.outside x →
    beta*(lower data x.1 : ℝ) ≤ endpointDegree l r v
  outside_upper : ∀ x v, vertexColumn d v=.outside x →
    endpointDegree l r v ≤ beta*(upper data x.1 : ℝ)
  center_degree : ∀ v, IsCenterColumn (vertexColumn d v) → endpointDegree l r v ≤ beta
  positive_degree : ∀ v, PositiveOutside (vertexColumn d v) → beta/256 ≤ endpointDegree l r v
  root_degree : ∀ i, d.kind i=.root → beta*(1-(data.lam : ℝ)) ≤
    endpointDegree l r (.inl (i,0))+endpointDegree l r (.inl (i,1))
  missing_degree : ∀ i, d.kind i=.missing → beta*(1-(data.lam : ℝ)) ≤
    endpointDegree l r (.inl (i,0))+endpointDegree l r (.inl (i,1))

theorem ProfileGeometry.reference_shape {d : Coordinates B U q} {ref : E → Column q}
    {l r : E → Vertex B U} {data : ProfileData q} {beta : ℝ}
    (h : ProfileGeometry d ref l r data beta) (e : E) :
    (∃ c x, ref e=.cross c x) ∨ (∃ c f, ref e=.internal c f) :=
  RobustMatching.R7SupportFlowMap.reference_shape _ _ _ (h.compatible e)

theorem graphPrimal_inequalities
    (d : Coordinates B U q) (ref : E → Column q) (l r : E → Vertex B U)
    (data : ProfileData q) (beta value : ℝ)
    (h : ProfileGeometry d ref l r data beta)
    (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ))
    (hb : centerCount (vertexColumn d) ≤ (Fintype.card B : ℝ))
    (hbase : centerCount (vertexColumn d)/(Fintype.card B : ℝ) ≤ value)
    (hphase : rawProfile d ref data beta/(Fintype.card B : ℝ) ≤ value)
    (hvalue : value ≤ 1) (hmass : 263 ≤ data.massBound) (row : LeRow q) :
    (∑ c, (coeffLe data row c : ℝ)*graphPrimal d ref beta value c) ≤ (rhsLe data row : ℝ) := by
  cases row with
  | centerLower c =>
      simpa [rhsLe] using graphPrimal_centerLower d ref l r data h.compatible
        beta value hbeta hmu c (h.center_lower c)
  | centerUpper c =>
      simpa [rhsLe] using graphPrimal_centerUpper d ref l r data h.compatible
        beta value hbeta hmu c (h.center_upper c)
  | outsideLower x =>
      simpa [rhsLe] using graphPrimal_outsideLower d ref l r data h.compatible
        beta value hbeta hmu x (h.outside_lower x)
  | outsideUpper x =>
      simpa [rhsLe] using graphPrimal_outsideUpper d ref l r data h.compatible
        beta value hbeta hmu x (h.outside_upper x)
  | baseValue => rw [graphPrimal_baseValue_formula d ref h.reference_shape]; simpa [rhsLe] using sub_nonpos.mpr hbase
  | baseOne => rw [graphPrimal_baseOne_formula d ref h.reference_shape]
               simpa [rhsLe] using (div_le_one hmu).mpr hb
  | valueOne => rw [graphPrimal_valueOne_formula d ref h.reference_shape]; simpa [rhsLe] using hvalue
  | rootMoment =>
      simpa [rhsLe] using graphPrimal_rootMoment d ref l r data h.compatible
        beta value hbeta hmu h.root_degree
  | missingMoment =>
      simpa [rhsLe] using graphPrimal_missingMoment d ref l r data h.compatible
        beta value hbeta hmu h.missing_degree
  | mass =>
      simpa [rhsLe] using graphPrimal_mass d ref l r data h.compatible beta value
        hbeta hmu hvalue hb h.center_degree h.positive_degree hmass
  | phase => rw [graphPrimal_phase_formula d ref data beta value hbeta hmu]
             simpa [rhsLe] using sub_nonpos.mpr hphase

/-- A graph-local certificate theorem: no linear-program feasibility or dual
inequalities are supplied by its caller. The degree/bin and incidence
hypotheses are the only geometric inputs. -/
theorem concrete_graph_profile_bound
    (d : Coordinates B U 152) (ref : E → Column 152) (l r : E → Vertex B U)
    (beta : ℝ) (h : ProfileGeometry d ref l r Concrete.data beta)
    (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ)) :
    (Concrete.target : ℝ)*(Fintype.card B : ℝ) ≤
      max (centerCount (vertexColumn d)) (rawProfile d ref Concrete.data beta) := by
  classical
  let b := centerCount (vertexColumn d)
  let f := rawProfile d ref Concrete.data beta
  let mu : ℝ := Fintype.card B
  have ht : (Concrete.target : ℝ) ≤ 1 := by norm_num [Concrete.target]
  by_cases hbig : mu ≤ max b f
  · exact (mul_le_of_le_one_left hmu.le ht).trans hbig
  have hb : b ≤ mu := (le_max_left b f).trans (le_of_lt (lt_of_not_ge hbig))
  have hf : f ≤ mu := (le_max_right b f).trans (le_of_lt (lt_of_not_ge hbig))
  let value := max (b/mu) (f/mu)
  have hv1 : value ≤ 1 := max_le ((div_le_one hmu).mpr hb) ((div_le_one hmu).mpr hf)
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun v _ => centerMark_nonneg _
  have hv0 : 0 ≤ value := (div_nonneg hb0 hmu.le).trans (le_max_left _ _)
  have hx := Concrete.exact_profile_certificate (graphPrimal d ref beta value)
    (graphPrimal_nonneg d ref hbeta hv0)
    (graphPrimal_support d ref Concrete.data beta value h.vertex_allowed h.benchmark_allowed h.reference_allowed)
    (graphPrimal_equalities d ref h.reference_shape hmu)
    (graphPrimal_inequalities d ref l r Concrete.data beta value h hbeta hmu hb
      (le_max_left _ _) (le_max_right _ _) hv1 (by norm_num [Concrete.data]))
  rw [graphPrimal_value d ref h.reference_shape] at hx
  have hm := mul_le_mul_of_nonneg_right hx hmu.le
  have he : value*mu=max b f := by
    dsimp [value]
    rw [max_mul_of_nonneg _ _ hmu.le]
    dsimp only [mu]
    field_simp [ne_of_gt hmu]
  change (Concrete.target : ℝ)*mu ≤ value*mu at hm
  rw [he] at hm
  exact hm

end Graph
end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.concrete_graph_profile_bound
