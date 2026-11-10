import RandomOrderMatching.Analysis.Profile.GraphObjective
import RandomOrderMatching.Analysis.Profile.Monotonicity

noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Graph RandomOrderMatching.Certificates.DegreeProfile
open RandomOrderMatching.Analysis.Repair.Labeling

section Actual
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
variable (M : Graph V) (hM : Matching M) (C : Finset V) (available : Graph V)
  (bin : V → Fin q) (mask : V → Fin 4)
local notation "D" => coordinatesFromMatching M hM C available bin mask

theorem actual_reference_column_count (H : Graph V) (x : CanonicalOutsides D) :
    (∑ c : CanonicalCenters D,
      if actualReferenceAdj M hM C available bin mask H c x then (1 : ℝ) else 0) ≤
      incidenceDegree H (actualVertexEquiv M hM C available bin mask (.inr x)) := by
  let A := Finset.univ.filter fun c : CanonicalCenters D =>
    actualReferenceAdj M hM C available bin mask H c x
  let f := fun c : CanonicalCenters D => actualReferenceEdge M hM C available bin mask c x
  have hf : Function.Injective f := by
    intro c c' hh
    have hp : (c,x)=(c',x) := actual_reference_pair_injective M hM C available bin mask hh
    exact congrArg Prod.fst hp
  have hsub : A.image f ⊆ H.filter (fun e => actualVertexEquiv M hM C available bin mask (.inr x)∈e.val) := by
    intro e he
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    constructor
    · exact (Finset.mem_filter.mp hc).2
    · simp [f,actual_reference_endpoints]
  have hcnt : (∑ c : CanonicalCenters D,
      if actualReferenceAdj M hM C available bin mask H c x then (1 : ℝ) else 0) = (A.card : ℝ) := by
    simp [A,Finset.sum_boole]
  rw [hcnt,incidenceDegree_eq_card]
  have himg : (A.image f).card=A.card := Finset.card_image_iff.mpr hf.injOn
  exact_mod_cast (show A.card ≤ (H.filter (fun e => actualVertexEquiv M hM C available bin mask (.inr x)∈e.val)).card by
    rw [←himg]
    exact Finset.card_le_card hsub)

theorem actual_binWeight_le_referenceWeight (H : Graph V) (data : ProfileData q)
    (beta : ℝ) (a : V → ℝ) (hbeta : 0 < beta) (hcap : 0 < data.cap)
    (hbin : ∀ v, (lower data (bin v) : ℝ) ≤ a v)
    (c : CanonicalCenters D) (x : CanonicalOutsides D) :
    binWeight D data beta (actualReferenceAdj M hM C available bin mask H) c x ≤
      RandomOrderMatching.Analysis.Repair.Typed.referenceWeight
        (fun x c => actualReferenceAdj M hM C available bin mask H c x) beta (data.cap : ℝ)
        (fun x => a (actualVertexEquiv M hM C available bin mask (.inr x))) c x := by
  rw [actual_reference_weight]
  have hh := binWeight_le_actual D data beta (actualReferenceAdj M hM C available bin mask H)
    (fun x => a (actualVertexEquiv M hM C available bin mask (.inr x))) hbeta hcap
    (fun x => hbin (actualVertexEquiv M hM C available bin mask (.inr x))) c x
  by_cases he : actualReferenceEdge M hM C available bin mask c x ∈ H
  · have ha : actualReferenceAdj M hM C available bin mask H c x := he
    simpa only [if_pos he,if_pos ha] using hh
  · have ha : ¬actualReferenceAdj M hM C available bin mask H c x := he
    simpa only [if_neg he,if_neg ha] using hh

end Actual
end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.actual_reference_column_count
#print axioms RandomOrderMatching.Analysis.Profile.actual_binWeight_le_referenceWeight
