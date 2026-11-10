import RandomOrderMatching.Analysis.Profile.Incidence
import RandomOrderMatching.Analysis.Profile.GraphCoordinates

/-! Actual incidence bounds for the finite mass constraint. The number of
unmatched degree-zero vertices is deliberately never bounded. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Certificates.DegreeProfile

instance {q} (v : Column q) : Decidable (IsCenterColumn v) := by
  cases v <;> unfold IsCenterColumn <;> infer_instance

def centerMark {q} (v : Column q) : ℝ := if IsCenterColumn v then 1 else 0

theorem reference_center_count {q} (u v e : Column q)
    (h : ReferenceCompatible u v e) : 1 ≤ centerMark u+centerMark v := by
  rcases h with ⟨a,b,rfl,rfl,_⟩ | ⟨a,x,rfl,rfl,_⟩ | ⟨a,x,rfl,rfl,_⟩ <;>
    norm_num [centerMark,IsCenterColumn]

theorem reference_outside_count {q} (u v e : Column q)
    (h : ReferenceCompatible u v e) :
    (1-centerMark u)+(1-centerMark v) ≤ centerMark u+centerMark v := by
  have hh := reference_center_count u v e h
  linarith

section Incidence
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] {q : ℕ}

def centerCount (tag : V → Column q) : ℝ := ∑ v, centerMark (tag v)

theorem reference_count_le_center_degree
    (tag : V → Column q) (ref : E → Column q) (l r : E → V)
    (h : ∀ e, ReferenceCompatible (tag (l e)) (tag (r e)) (ref e)) :
    (Fintype.card E : ℝ) ≤ ∑ v, centerMark (tag v)*endpointDegree l r v := by
  rw [endpointDegree_sum]
  calc
    (Fintype.card E : ℝ) = ∑ _e : E, (1 : ℝ) := by simp
    _ ≤ ∑ e, (centerMark (tag (l e))+centerMark (tag (r e))) :=
      Finset.sum_le_sum fun e _ => reference_center_count _ _ _ (h e)

theorem outside_degree_le_center_degree
    (tag : V → Column q) (ref : E → Column q) (l r : E → V)
    (h : ∀ e, ReferenceCompatible (tag (l e)) (tag (r e)) (ref e)) :
    (∑ v, (1-centerMark (tag v))*endpointDegree l r v) ≤
      ∑ v, centerMark (tag v)*endpointDegree l r v := by
  rw [endpointDegree_sum,endpointDegree_sum]
  exact Finset.sum_le_sum fun e _ => reference_outside_count _ _ _ (h e)

theorem center_degree_le_count (tag : V → Column q) (l r : E → V)
    (beta : ℝ) (h : ∀ v, IsCenterColumn (tag v) → endpointDegree l r v ≤ beta) :
    (∑ v, centerMark (tag v)*endpointDegree l r v) ≤ beta*centerCount tag := by
  unfold centerCount
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : IsCenterColumn (tag v)
  · simpa [centerMark,hv] using h v hv
  · simp [centerMark,hv]

theorem reference_count_le_beta_centers
    (tag : V → Column q) (ref : E → Column q) (l r : E → V)
    (hRef : ∀ e, ReferenceCompatible (tag (l e)) (tag (r e)) (ref e))
    (beta : ℝ) (hdegree : ∀ v, IsCenterColumn (tag v) → endpointDegree l r v ≤ beta) :
    (Fintype.card E : ℝ) ≤ beta*centerCount tag :=
  (reference_count_le_center_degree tag ref l r hRef).trans
    (center_degree_le_count tag l r beta hdegree)

theorem outside_degree_le_beta_centers
    (tag : V → Column q) (ref : E → Column q) (l r : E → V)
    (hRef : ∀ e, ReferenceCompatible (tag (l e)) (tag (r e)) (ref e))
    (beta : ℝ) (hdegree : ∀ v, IsCenterColumn (tag v) → endpointDegree l r v ≤ beta) :
    (∑ v, (1-centerMark (tag v))*endpointDegree l r v) ≤ beta*centerCount tag :=
  (outside_degree_le_center_degree tag ref l r hRef).trans
    (center_degree_le_count tag l r beta hdegree)

/-- Any set of outside vertices whose normalized degree is at least1/256
has cardinality at most256b. No assertion is made about the other vertices. -/
theorem positive_outside_count
    (tag : V → Column q) (ref : E → Column q) (l r : E → V)
    (hRef : ∀ e, ReferenceCompatible (tag (l e)) (tag (r e)) (ref e))
    (A : Finset V) (beta : ℝ) (hbeta : 0 < beta)
    (hdegree : ∀ v, IsCenterColumn (tag v) → endpointDegree l r v ≤ beta)
    (hout : ∀ v ∈ A, ¬IsCenterColumn (tag v))
    (hlower : ∀ v ∈ A, beta/256 ≤ endpointDegree l r v) :
    (A.card : ℝ) ≤ 256*centerCount tag := by
  let a : V → ℝ := fun v => (1-centerMark (tag v))*endpointDegree l r v
  have ha : ∀ v, 0 ≤ a v := by
    intro v
    by_cases hv : IsCenterColumn (tag v)
    · simp [a,centerMark,hv]
    · simpa [a,centerMark,hv] using endpointDegree_nonneg l r v
  have hlo : ∀ v ∈ A, beta/256 ≤ a v := by
    intro v hv
    simpa [a,centerMark,hout v hv] using hlower v hv
  have ht : (∑ v, a v) ≤ beta*centerCount tag :=
    outside_degree_le_beta_centers tag ref l r hRef beta hdegree
  have hh := positive_degree_count A a (beta/256) (beta*centerCount tag)
    (by positivity) ha hlo ht
  have heq : (beta*centerCount tag)/(beta/256)=256*centerCount tag := by
    field_simp [ne_of_gt hbeta]
  simpa [heq] using hh

end Incidence
end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.reference_count_le_beta_centers
#print axioms RandomOrderMatching.Analysis.Profile.positive_outside_count
