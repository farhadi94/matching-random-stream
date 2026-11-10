import RobustMatching.R7SupportFlowMapCoordinates

/-! The concrete primal vector is the pushforward of vertex, reference-edge
and benchmark-pair records. Every semantic equality row is proved. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7SupportFlowMap
open RobustMatching.R7ReductionCertificate

variable {B U E : Type*} [Fintype B] [Fintype U] [Fintype E]
  [DecidableEq B] [DecidableEq U] {q : ℕ}

def rawVertices (d : Coordinates B U q) : Column q → ℝ :=
  pushMass Finset.univ (vertexColumn d) (fun _ => 1)
def rawBenchmark (d : Coordinates B U q) : Column q → ℝ :=
  pushMass Finset.univ (benchmarkColumn d) (fun i => pairWeight (d.kind i))
def rawReference (ref : E → Column q) : Column q → ℝ :=
  pushMass Finset.univ ref (fun _ => 1)
def internalCount (d : Coordinates B U q) : ℝ := ∑ i, internalWeight (d.kind i)

def graphPrimal (d : Coordinates B U q) (ref : E → Column q)
    (beta value : ℝ) (c : Column q) : ℝ :=
  (rawVertices d c+rawBenchmark d c+(if c=.z then internalCount d else 0)) /
    (Fintype.card B : ℝ) +
  rawReference ref c / (beta*(Fintype.card B : ℝ))+
  (if c=.value then value else 0)

theorem graphPrimal_eval (d : Coordinates B U q) (ref : E → Column q)
    (beta value : ℝ) (f : Column q → ℝ) :
    (∑ c, f c*graphPrimal d ref beta value c) =
      ((∑ v, f (vertexColumn d v))+
       (∑ i, pairWeight (d.kind i)*f (benchmarkColumn d i))+
       internalCount d*f .z)/(Fintype.card B : ℝ)+
       (∑ e, f (ref e))/(beta*(Fintype.card B : ℝ))+f .value*value := by
  have hp : ∀ c, f c*graphPrimal d ref beta value c =
      (f c*rawVertices d c+f c*rawBenchmark d c+
        (if c=.z then internalCount d*f c else 0))/(Fintype.card B : ℝ)+
      (f c*rawReference ref c)/(beta*(Fintype.card B : ℝ))+
      (if c=.value then f c*value else 0) := by
    intro c
    unfold graphPrimal
    split_ifs <;> ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    ←Finset.sum_div,←Finset.sum_div]
  simp only [Finset.sum_add_distrib]
  unfold rawVertices rawBenchmark rawReference
  rw [pushMass_eval, pushMass_eval, pushMass_eval]
  simp [eq_comm, mul_comm, rawVertices, rawBenchmark, rawReference]

theorem pairWeight_nonneg (k : PairKind) : 0 ≤ pairWeight k := by cases k <;> norm_num [pairWeight]
theorem internalWeight_nonneg (k : PairKind) : 0 ≤ internalWeight k := by
  cases k <;> norm_num [internalWeight]

theorem graphPrimal_nonneg (d : Coordinates B U q) (ref : E → Column q)
    {beta value : ℝ} (hbeta : 0 < beta) (hvalue : 0 ≤ value) (c : Column q) :
    0 ≤ graphPrimal d ref beta value c := by
  have hv : 0 ≤ rawVertices d c := pushMass_nonneg _ _ _ (by intros; norm_num) _
  have hb : 0 ≤ rawBenchmark d c := pushMass_nonneg _ _ _
    (fun i _ => pairWeight_nonneg _) _
  have hr : 0 ≤ rawReference ref c := pushMass_nonneg _ _ _ (by intros; norm_num) _
  have hi : 0 ≤ internalCount d := Finset.sum_nonneg fun i _ => internalWeight_nonneg _
  unfold graphPrimal
  split_ifs <;> positivity

theorem graphPrimal_equalities (d : Coordinates B U q) (ref : E → Column q)
    (hRef : ∀ e, (∃ c x, ref e=.cross c x) ∨ (∃ c f, ref e=.internal c f))
    {beta value : ℝ} (hmu : 0 < (Fintype.card B : ℝ)) (r : EqRow q) :
    (∑ c, (coeffEq r c : ℝ)*graphPrimal d ref beta value c) = (rhsEq r : ℝ) := by
  rw [graphPrimal_eval]
  have hr : (∑ e, (coeffEq r (ref e) : ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro e _
    rcases hRef e with ⟨c,x,hh⟩ | ⟨c,f,hh⟩ <;>
      simp [hh,coeffEq,eqTerms,coeff]
  have hval : (coeffEq r .value : ℝ)=0 := by simp [coeffEq,eqTerms,coeff]
  rw [hr,hval,zero_div,zero_mul,add_zero,add_zero]
  simp only [internalCount]
  rw [coordinate_eq_balance]
  field_simp [ne_of_gt hmu]

theorem graphPrimal_support (d : Coordinates B U q) (ref : E → Column q)
    (data : ProfileData q) (beta value : ℝ)
    (hv : ∀ v, columnAllowed data (vertexColumn d v))
    (hb : ∀ i, columnAllowed data (benchmarkColumn d i))
    (hr : ∀ e, columnAllowed data (ref e))
    (c : Column q) (hc : ¬columnAllowed data c) :
    graphPrimal d ref beta value c=0 := by
  have hvc : rawVertices d c=0 := pushMass_forbidden_zero _ _ _ _ (fun v _ => hv v) _ hc
  have hbc : rawBenchmark d c=0 := pushMass_forbidden_zero _ _ _ _ (fun i _ => hb i) _ hc
  have hrc : rawReference ref c=0 := pushMass_forbidden_zero _ _ _ _ (fun e _ => hr e) _ hc
  have hz : c ≠ .z := by intro hh; subst c; exact hc (by trivial)
  have hvalue : c ≠ .value := by intro hh; subst c; exact hc (by trivial)
  simp [graphPrimal,hvc,hbc,hrc,hz,hvalue]

end RobustMatching.R7SupportFlowMap

#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_equalities
#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_nonneg
#print axioms RobustMatching.R7SupportFlowMap.graphPrimal_support
