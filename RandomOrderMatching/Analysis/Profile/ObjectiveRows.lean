import RandomOrderMatching.Analysis.Profile.CountingRows

/-! Base, value and phase rows. The LP value is explicitly chosen as the
maximum of the actual base count and the bin-lowered repair expression. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Certificates.DegreeProfile

theorem vertex_base_credit {q} (data : ProfileData q) (k : Column q) (h : IsVertexColumn k) :
    (coeffLe data .baseOne k : ℝ)=centerMark k := by
  cases k <;> simp [IsVertexColumn] at h <;>
    simp [coeffLe,leTerms,coeff,centerMark,IsCenterColumn]

theorem benchmark_control_zero {q} (data : ProfileData q) (k : PairKind)
    (b0 b1 : Fin q) (m0 m1 : Fin 4) :
    coeffLe data .baseOne (pairColumn k b0 b1 m0 m1)=0 ∧
    pairColumn k b0 b1 m0 m1 ≠ .value := by
  cases k <;> simp [pairColumn,orderedRoot,orderedPair,coeffLe,leTerms,coeff] <;>
    split_ifs <;> simp [coeff]

theorem reference_shape {q} (u v e : Column q) (h : ReferenceCompatible u v e) :
    (∃ c x, e=.cross c x) ∨ (∃ c d, e=.internal c d) := by
  rcases h with ⟨c,d,_,_,h | h⟩ | ⟨c,x,_,_,h⟩ | ⟨c,x,_,_,h⟩
  · exact Or.inr ⟨c,d,h⟩
  · exact Or.inr ⟨d,c,h⟩
  · exact Or.inl ⟨c,x,h⟩
  · exact Or.inl ⟨c,x,h⟩

theorem valueOne_coeff {q} (data : ProfileData q) (c : Column q) :
    (coeffLe data .valueOne c : ℝ)=(if c=.value then 1 else 0) := by
  cases c <;> simp [coeffLe,leTerms,coeff]

theorem baseValue_coeff {q} (data : ProfileData q) (c : Column q) :
    (coeffLe data .baseValue c : ℝ) =
      (coeffLe data .baseOne c : ℝ)-(coeffLe data .valueOne c : ℝ) := by
  cases c <;> simp [coeffLe,leTerms,coeff]

section Coordinates
variable {B U E : Type*} [Fintype B] [Fintype U] [Fintype E]
  [DecidableEq B] [DecidableEq U] {q : ℕ}

theorem graphPrimal_value (d : Coordinates B U q) (ref : E → Column q)
    (hRef : ∀ e, (∃ c x, ref e=.cross c x) ∨ (∃ c f, ref e=.internal c f))
    (beta value : ℝ) : graphPrimal d ref beta value .value=value := by
  have hv : rawVertices d .value=0 := by
    apply Finset.sum_eq_zero
    intro v _
    have hne : vertexColumn d v ≠ .value := by
      intro hh
      have hi := vertexColumn_is_vertex d v
      simpa [hh,IsVertexColumn] using hi
    simp [hne]
  have hb : rawBenchmark d .value=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hne : benchmarkColumn d i ≠ .value := by
      cases hk : d.kind i <;>
        simp [benchmarkColumn,hk,pairColumn,orderedRoot,orderedPair] <;>
        split_ifs <;> simp
    simp [hne]
  have hr : rawReference ref .value=0 := by
    apply Finset.sum_eq_zero
    intro e _
    rcases hRef e with ⟨c,x,hh⟩ | ⟨c,f,hh⟩ <;> simp [hh]
  simp [graphPrimal,hv,hb,hr]

theorem graphPrimal_baseOne_formula (d : Coordinates B U q) (ref : E → Column q)
    (hRef : ∀ e, (∃ c x, ref e=.cross c x) ∨ (∃ c f, ref e=.internal c f))
    (data : ProfileData q) (beta value : ℝ) :
    (∑ c, (coeffLe data .baseOne c : ℝ)*graphPrimal d ref beta value c) =
      centerCount (vertexColumn d)/(Fintype.card B : ℝ) := by
  rw [graphPrimal_eval]
  have hv : (∑ v, (coeffLe data .baseOne (vertexColumn d v) : ℝ))=centerCount (vertexColumn d) := by
    apply Finset.sum_congr rfl
    intro v _
    exact vertex_base_credit data _ (vertexColumn_is_vertex d v)
  have hb : (∑ i, pairWeight (d.kind i)*(coeffLe data .baseOne (benchmarkColumn d i) : ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hh := (benchmark_control_zero data (d.kind i) (d.bin (.inl (i,0))) (d.bin (.inl (i,1)))
        (d.mask (.inl (i,0))) (d.mask (.inl (i,1)))).1
    change pairWeight _*(coeffLe _ _ (pairColumn _ _ _ _ _) : ℝ)=0
    rw [hh]; norm_num
  have hr : (∑ e, (coeffLe data .baseOne (ref e) : ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro e _
    rcases hRef e with ⟨c,x,hh⟩ | ⟨c,f,hh⟩ <;> simp [hh,coeffLe,leTerms,coeff]
  rw [hv,hb,hr]
  simp [coeffLe,leTerms,coeff]

theorem graphPrimal_valueOne_formula (d : Coordinates B U q) (ref : E → Column q)
    (hRef : ∀ e, (∃ c x, ref e=.cross c x) ∨ (∃ c f, ref e=.internal c f))
    (data : ProfileData q) (beta value : ℝ) :
    (∑ c, (coeffLe data .valueOne c : ℝ)*graphPrimal d ref beta value c)=value := by
  simp_rw [valueOne_coeff]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact graphPrimal_value d ref hRef beta value

theorem graphPrimal_baseValue_formula (d : Coordinates B U q) (ref : E → Column q)
    (hRef : ∀ e, (∃ c x, ref e=.cross c x) ∨ (∃ c f, ref e=.internal c f))
    (data : ProfileData q) (beta value : ℝ) :
    (∑ c, (coeffLe data .baseValue c : ℝ)*graphPrimal d ref beta value c) =
      centerCount (vertexColumn d)/(Fintype.card B : ℝ)-value := by
  simp_rw [baseValue_coeff,sub_mul]
  rw [Finset.sum_sub_distrib,graphPrimal_baseOne_formula,graphPrimal_valueOne_formula]
  all_goals exact hRef

def rawProfile (d : Coordinates B U q) (ref : E → Column q) (data : ProfileData q) (beta : ℝ) : ℝ :=
  (∑ v, (coeffLe data .phase (vertexColumn d v) : ℝ))+
  (∑ i, pairWeight (d.kind i)*(coeffLe data .phase (benchmarkColumn d i) : ℝ))+
  (∑ e, (coeffLe data .phase (ref e) : ℝ))/beta

theorem graphPrimal_phase_formula (d : Coordinates B U q) (ref : E → Column q)
    (data : ProfileData q) (beta value : ℝ)
    (hbeta : 0 < beta) (hmu : 0 < (Fintype.card B : ℝ)) :
    (∑ c, (coeffLe data .phase c : ℝ)*graphPrimal d ref beta value c) =
      rawProfile d ref data beta/(Fintype.card B : ℝ)-value := by
  rw [graphPrimal_eval]
  have hz : coeffLe data .phase (.z : Column q)=0 := by simp [coeffLe,leTerms,coeff]
  have hv : coeffLe data .phase (.value : Column q)=(-1 : ℚ) := by simp [coeffLe,leTerms,coeff]
  rw [hz,hv]
  unfold rawProfile
  push_cast
  field_simp [ne_of_gt hbeta,ne_of_gt hmu]
  ring

end Coordinates
end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.graphPrimal_value
#print axioms RandomOrderMatching.Analysis.Profile.graphPrimal_baseOne_formula
#print axioms RandomOrderMatching.Analysis.Profile.graphPrimal_phase_formula
