import RandomOrderMatching.Analysis.Repair.GateCharges
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! Actual graph and matching specialization of the exact support charge.
Injectivity and root/partner disjointness are derived from `IsMatching`. -/
noncomputable section
open scoped BigOperators

namespace RandomOrderMatching.Analysis.Repair.Gates
open RandomOrderMatching.Analysis.Repair.Reference

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- In an actual matching, crossing-edge outside partners are injective and
cannot be endpoints of matching edges completely outside the cover. -/
theorem matching_partners_separate
    (G : SimpleGraph W) (opt : G.Subgraph) (hopt : opt.IsMatching)
    (C : Set W) [DecidablePred (· ∈ C)]
    (S : Finset {v : W // v ∉ C}) (M : Finset {v : W // v ∈ C})
    (partner : {v : W // v ∈ C} → {v : W // v ∉ C})
    (hroot : ∀ s ∈ S, ∃ t : {v : W // v ∉ C}, opt.Adj s.val t.val)
    (hedge : ∀ c ∈ M, opt.Adj c.val (partner c).val) :
    Set.InjOn partner (M : Set {v : W // v ∈ C}) ∧
      Disjoint S (M.image partner) := by
  constructor
  · intro c hc d hd heq
    apply Subtype.ext
    have hd' : opt.Adj d.val (partner c).val := by simpa only [heq] using hedge d hd
    exact hopt.eq_of_adj_right (hedge c hc) hd'
  · apply Finset.disjoint_left.mpr
    intro s hs hsm
    obtain ⟨c, hc, hcs⟩ := Finset.mem_image.mp hsm
    obtain ⟨t, ht⟩ := hroot s hs
    have hct : c.val = t.val := hopt.eq_of_adj_left
      (by simpa only [hcs] using (hedge c hc).symm) ht
    exact t.property (hct ▸ c.property)

/-- Exact gate bound on actual finite simple graphs and an actual matching.
Only reference degree bounds and the missed optimum-edge degree lower bound
are assumed; capacity, normalized domains and partner separation are proved. -/
theorem exact_missing_gate_count_of_graph
    (H G : SimpleGraph W) [DecidableRel H.Adj]
    (opt : G.Subgraph) (hopt : opt.IsMatching)
    (C : Set W) [DecidablePred (· ∈ C)] (hC : H.IsVertexCover C)
    {β lam D : ℝ} (hβ : 0 < β) (hD : 0 ≤ D)
    (hupper : ∀ u v, H.Adj u v → (H.degree u : ℝ)+H.degree v ≤ β)
    (S : Finset {v : W // v ∉ C}) (M : Finset {v : W // v ∈ C})
    (partner : {v : W // v ∈ C} → {v : W // v ∉ C})
    (hroot : ∀ s ∈ S, ∃ t : {v : W // v ∉ C}, opt.Adj s.val t.val)
    (hedge : ∀ c ∈ M, opt.Adj c.val (partner c).val)
    (hlower : ∀ c ∈ M, (1-lam)*β ≤
      (H.degree c.val : ℝ)+H.degree (partner c).val) :
    (M.card : ℝ) ≤
      (1+D)*(∑ c : {v : W // v ∈ C},
        (1-centerLoad
          (fun (s : {v : W // v ∉ C}) (c : {v : W // v ∈ C}) => H.Adj s.val c.val)
          β (fun s => (H.degree s.val : ℝ)/β) S c)) +
      ∑ s ∈ S, exactGateProfile lam D ((H.degree s.val : ℝ)/β) := by
  classical
  have hs := supportData_of_graph_cover H C hC hβ hupper
  obtain ⟨hinj, hdisj⟩ := matching_partners_separate G opt hopt C S M partner hroot hedge
  apply exact_missing_gate_count hs hD S M partner (fun c => 1-(H.degree c.val : ℝ)/β)
    hinj hdisj
  · intro c hc s hsm hadj
    have hh := hupper s.val c.val hadj
    apply (le_sub_iff_add_le).2
    rw [← add_div]
    exact (div_le_one hβ).2 hh
  · intro c hc
    apply max_le
    · have hh := hlower c hc
      have hh' : 1-lam ≤ ((H.degree c.val : ℝ)+H.degree (partner c).val)/β :=
        (le_div_iff₀ hβ).2 hh
      rw [add_div] at hh'
      linarith
    · exact div_nonneg (Nat.cast_nonneg _) hβ.le

end RandomOrderMatching.Analysis.Repair.Gates

#print axioms RandomOrderMatching.Analysis.Repair.Gates.matching_partners_separate
#print axioms RandomOrderMatching.Analysis.Repair.Gates.exact_missing_gate_count_of_graph
