import RobustMatching.R1GateBridge
import RobustMatching.R7ClosedRepairTypedLabelingReference
import RobustMatching.R8AcquisitionIncidence

/-! Construct the probability support interface from the actual reference
graph and cover. Center degrees in SupportData are unnormalized. -/
noncomputable section
set_option maxHeartbeats 400000
open Classical
open scoped BigOperators
namespace RobustMatching.R8FixedHostSupport
open RobustMatching.R2Cut RobustMatching.R1Gate RobustMatching.R7GraphKonig
open RobustMatching.R7GraphComponents RobustMatching.R7SupportFlowMap
open RobustMatching.R7ClosedRepair.TypedLabeling

theorem filter_card_equiv_real {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → Prop) :
    ((Finset.univ.filter fun a => p (e a)).card : ℝ)=
      ((Finset.univ.filter p).card : ℝ) := by
  simpa only [Finset.sum_boole] using e.sum_comp (fun b => if p b then (1 : ℝ) else 0)

theorem supportData_relabel {O C O' C' : Type*}
    [Fintype O] [Fintype C] [Fintype O'] [Fintype C']
    [DecidableEq O] [DecidableEq C] [DecidableEq O'] [DecidableEq C']
    (eO : O' ≃ O) (eC : C' ≃ C) (adj : O → C → Prop) (adj' : O' → C' → Prop)
    (beta : ℝ) (a : O → ℝ) (dc : C → ℝ)
    (h : SupportData adj beta a dc)
    (hadj : ∀ x c, adj' x c ↔ adj (eO x) (eC c)) :
    SupportData adj' beta (fun x => a (eO x)) (fun c => dc (eC c)) := by
  constructor
  · exact h.beta_pos
  · exact fun x => h.degree_nonneg (eO x)
  · exact fun x => h.degree_lt_one (eO x)
  · intro x
    have hf : Finset.univ.filter (adj' x) =
        Finset.univ.filter (fun c => adj (eO x) (eC c)) := by
      ext c; simp only [Finset.mem_filter,Finset.mem_univ,true_and,hadj]
    rw [hf,filter_card_equiv_real eC (adj (eO x))]
    exact h.row_degree (eO x)
  · intro c
    have hf : Finset.univ.filter (fun x => adj' x c) =
        Finset.univ.filter (fun x => adj (eO x) (eC c)) := by
      ext x; simp only [Finset.mem_filter,Finset.mem_univ,true_and,hadj]
    rw [hf,filter_card_equiv_real eO (fun x => adj x (eC c))]
    exact h.column_degree (eC c)
  · exact fun x c hh => h.edge_degree (eO x) (eC c) ((hadj x c).mp hh)

section Actual
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
variable (M : Graph V) (hM : Matching M) (C : Finset V) (available : Graph V)
  (bin : V → Fin q) (mask : V → Fin 4)
local notation "D" => coordinatesFromMatching M hM C available bin mask

theorem actual_reference_adj_iff (H : Graph V) (c : CanonicalCenters D) (x : CanonicalOutsides D) :
    actualReferenceAdj M hM C available bin mask H c x ↔
      (simpleGraph H).Adj
        (actualVertexEquiv M hM C available bin mask (.inr x))
        (actualVertexEquiv M hM C available bin mask (.inl c)) := by
  constructor
  · intro he
    apply adj_of_edge he
    · simp [actual_reference_endpoints]
    · simp [actual_reference_endpoints]
    · intro hh
      have h := (actualVertexEquiv M hM C available bin mask).injective hh
      cases h
  · rintro ⟨⟨e,he,hev⟩,hne⟩
    have heq : actualReferenceEdge M hM C available bin mask c x=e := by
      apply Subtype.ext
      rw [actual_reference_endpoints]
      rw [Finset.pair_comm]
      simpa only [Sym2.toFinset_mk_eq] using hev
    change actualReferenceEdge M hM C available bin mask c x∈H
    rw [heq]
    exact he

theorem actual_cover_simpleGraph (H : Graph V)
    (hcover : ∀ e∈H, ∃ v∈e.val, v∈C) :
    (simpleGraph H).IsVertexCover (C : Set V) := by
  intro u v huv
  obtain ⟨⟨e,he,hev⟩,hne⟩ := huv
  obtain ⟨z,hze,hzC⟩ := hcover e he
  have hp : e.val={u,v} := by simpa only [Sym2.toFinset_mk_eq] using hev.symm
  rw [hp] at hze
  rcases Finset.mem_insert.mp hze with hz | hz
  · left; simpa [←hz] using hzC
  · right; simpa [Finset.mem_singleton.mp hz] using hzC

theorem incidenceDegree_eq_simpleGraph (H : Graph V) (v : V) :
    incidenceDegree H v=((simpleGraph H).degree v : ℝ) := by
  rw [RobustMatching.R8Acquisition.simpleGraph_degree,incidenceDegree_eq_card]
  rfl

theorem actual_upper_simpleGraph (H : Graph V) (beta : ℝ)
    (hupper : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta) :
    ∀ u v, (simpleGraph H).Adj u v →
      ((simpleGraph H).degree u : ℝ)+(simpleGraph H).degree v ≤ beta := by
  intro u v ha
  obtain ⟨⟨e,he,hev⟩,hne⟩ := ha
  have hp : e.val={u,v} := by simpa only [Sym2.toFinset_mk_eq] using hev.symm
  have hn : orientedEndpoint C e 0 ≠ orientedEndpoint C e 1 := by
    intro hh
    have hi := (endpoint_injective e) hh
    have hi' := (coverOrder C e).injective hi
    norm_num at hi'
  have h0 : (∑ z∈e.val, incidenceDegree H z)=incidenceDegree H u+incidenceDegree H v := by
    rw [hp]; simp [hne]
  have h1 : (∑ z∈e.val, incidenceDegree H z)=
      incidenceDegree H (orientedEndpoint C e 0)+incidenceDegree H (orientedEndpoint C e 1) := by
    rw [←oriented_endpoint_pair C e]; simp [hn]
  rw [←incidenceDegree_eq_simpleGraph,←incidenceDegree_eq_simpleGraph,←h0,h1]
  exact hupper e he

/-- Concrete support data for the exact typed labels used in the final
profile. The full outside degree is counted because C covers every H edge;
the center degree includes internal cover edges. -/
theorem actual_reference_supportData (H : Graph V) (beta : ℝ) (hbeta : 0 < beta)
    (hcover : ∀ e∈H, ∃ v∈e.val, v∈C)
    (hupper : ∀ e∈H, incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) ≤ beta) :
    SupportData (fun x c => actualReferenceAdj M hM C available bin mask H c x) beta
      (fun x => incidenceDegree H (actualVertexEquiv M hM C available bin mask (.inr x))/beta)
      (fun c => incidenceDegree H (actualVertexEquiv M hM C available bin mask (.inl c))) := by
  have hs := supportData_of_graph_cover (simpleGraph H) (C : Set V)
    (actual_cover_simpleGraph C H hcover) hbeta (actual_upper_simpleGraph C H beta hupper)
  have hf : (Subtype.fintype (fun v : V => v ∈ (C : Set V))) =
      (inferInstance : Fintype {v : V // v ∈ (C : Set V)}) := Subsingleton.elim _ _
  rw [hf] at hs
  have ht := supportData_relabel (O := {v : V // v ∉ (C : Set V)}) (C := {v : V // v ∈ (C : Set V)})
    (actualOutsideEquiv M hM C available bin mask) (actualCoverEquiv M hM C available bin mask)
    (fun x c => (simpleGraph H).Adj x.val c.val)
    (fun x c => actualReferenceAdj M hM C available bin mask H c x) beta
    (fun x => ((simpleGraph H).degree x.val : ℝ)/beta)
    (fun c => ((simpleGraph H).degree c.val : ℝ)) hs
    (fun x c => actual_reference_adj_iff M hM C available bin mask H c x)
  change SupportData (fun x c => actualReferenceAdj M hM C available bin mask H c x) beta
    (fun x => ((simpleGraph H).degree (actualVertexEquiv M hM C available bin mask (.inr x)) : ℝ)/beta)
    (fun c => ((simpleGraph H).degree (actualVertexEquiv M hM C available bin mask (.inl c)) : ℝ)) at ht
  simpa only [←incidenceDegree_eq_simpleGraph] using ht

end Actual
end RobustMatching.R8FixedHostSupport

#print axioms RobustMatching.R8FixedHostSupport.actual_reference_supportData
