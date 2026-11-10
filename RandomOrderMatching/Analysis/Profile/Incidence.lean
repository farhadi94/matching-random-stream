import RandomOrderMatching.Analysis.Profile.Primal

/-! Pointwise reference-edge semantics and actual indexed incidence sums.
Internal class pairs contribute twice when both endpoints have the class. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Certificates.DegreeProfile

def ReferenceCompatible {q} (u v e : Column q) : Prop :=
  (∃ c d, u=.center c ∧ v=.center d ∧ (e=.internal c d ∨ e=.internal d c)) ∨
  (∃ c x, u=.center c ∧ v=.outside x ∧ e=.cross c x) ∨
  (∃ c x, v=.center c ∧ u=.outside x ∧ e=.cross c x)

theorem reference_center_lower {q} (data : ProfileData q) (u v e : Column q)
    (h : ReferenceCompatible u v e) (c : CenterClass q) :
    (coeffLe data (.centerLower c) e : ℝ) =
      -(if u=.center c then 1 else 0)-(if v=.center c then 1 else 0) := by
  rcases h with ⟨a,b,rfl,rfl,hh | hh⟩ | ⟨a,x,rfl,rfl,rfl⟩ | ⟨a,x,rfl,rfl,rfl⟩ <;>
    try subst e
  all_goals simp [coeffLe,leTerms,coeff] <;> split_ifs <;> norm_num

theorem reference_center_upper {q} (data : ProfileData q) (u v e : Column q)
    (h : ReferenceCompatible u v e) (c : CenterClass q) :
    (coeffLe data (.centerUpper c) e : ℝ) =
      (if u=.center c then 1 else 0)+(if v=.center c then 1 else 0) := by
  rcases h with ⟨a,b,rfl,rfl,hh | hh⟩ | ⟨a,x,rfl,rfl,rfl⟩ | ⟨a,x,rfl,rfl,rfl⟩ <;>
    try subst e
  all_goals simp [coeffLe,leTerms,coeff] <;> split_ifs <;> norm_num

theorem reference_outside_lower {q} (data : ProfileData q) (u v e : Column q)
    (h : ReferenceCompatible u v e) (x : OutsideClass q) :
    (coeffLe data (.outsideLower x) e : ℝ) =
      -(if u=.outside x then 1 else 0)-(if v=.outside x then 1 else 0) := by
  rcases h with ⟨a,b,rfl,rfl,hh | hh⟩ | ⟨a,y,rfl,rfl,rfl⟩ | ⟨a,y,rfl,rfl,rfl⟩ <;>
    try subst e
  all_goals simp [coeffLe,leTerms,coeff] <;> split_ifs <;> norm_num

theorem reference_outside_upper {q} (data : ProfileData q) (u v e : Column q)
    (h : ReferenceCompatible u v e) (x : OutsideClass q) :
    (coeffLe data (.outsideUpper x) e : ℝ) =
      (if u=.outside x then 1 else 0)+(if v=.outside x then 1 else 0) := by
  rcases h with ⟨a,b,rfl,rfl,hh | hh⟩ | ⟨a,y,rfl,rfl,rfl⟩ | ⟨a,y,rfl,rfl,rfl⟩ <;>
    try subst e
  all_goals simp [coeffLe,leTerms,coeff] <;> split_ifs <;> norm_num

def endpointDegree {V E : Type*} [DecidableEq V] [Fintype E]
    (l r : E → V) (v : V) : ℝ :=
  ∑ e, ((if l e=v then 1 else 0)+(if r e=v then 1 else 0))

theorem endpointDegree_nonneg {V E : Type*} [DecidableEq V] [Fintype E]
    (l r : E → V) (v : V) : 0 ≤ endpointDegree l r v := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> norm_num

theorem endpointDegree_sum {V E : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    (l r : E → V) (f : V → ℝ) :
    (∑ v, f v*endpointDegree l r v) = ∑ e, (f (l e)+f (r e)) := by
  simp only [endpointDegree,Finset.mul_sum,mul_add,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [Finset.sum_add_distrib,eq_comm]

theorem endpointDegree_class_sum {V E K : Type*} [DecidableEq V]
    [DecidableEq K] [Fintype V] [Fintype E]
    (l r : E → V) (tag : V → K) (k : K) :
    pushMass Finset.univ tag (endpointDegree l r) k =
      ∑ e, ((if tag (l e)=k then 1 else 0)+(if tag (r e)=k then 1 else 0)) := by
  have hh := endpointDegree_sum l r (fun v => if tag v=k then 1 else 0)
  simpa [pushMass,ite_mul] using hh

theorem reference_center_degree_sum {q V E} [DecidableEq V]
    [Fintype V] [Fintype E]
    (data : ProfileData q) (tag : V → Column q) (ref : E → Column q)
    (l r : E → V) (h : ∀ e, ReferenceCompatible (tag (l e)) (tag (r e)) (ref e))
    (c : CenterClass q) :
    (∑ e, (coeffLe data (.centerLower c) (ref e) : ℝ)) =
      -pushMass Finset.univ tag (endpointDegree l r) (.center c) := by
  rw [endpointDegree_class_sum]
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [reference_center_lower data _ _ _ (h e) c]
  ring

theorem reference_outside_degree_sum {q V E} [DecidableEq V]
    [Fintype V] [Fintype E]
    (data : ProfileData q) (tag : V → Column q) (ref : E → Column q)
    (l r : E → V) (h : ∀ e, ReferenceCompatible (tag (l e)) (tag (r e)) (ref e))
    (x : OutsideClass q) :
    (∑ e, (coeffLe data (.outsideLower x) (ref e) : ℝ)) =
      -pushMass Finset.univ tag (endpointDegree l r) (.outside x) := by
  rw [endpointDegree_class_sum]
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [reference_outside_lower data _ _ _ (h e) x]
  ring

end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.reference_center_degree_sum
#print axioms RandomOrderMatching.Analysis.Profile.reference_outside_degree_sum
