import RandomOrderMatching.Analysis.Repair.ReferenceSupport
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Finite

noncomputable section

namespace RandomOrderMatching.Analysis.Repair.Reference

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The normalized degree is strictly less than one at every vertex, including
isolates, from the actual reference graph's upper edge-degree constraint. -/
theorem normalized_degree_lt_one (H : SimpleGraph W) [DecidableRel H.Adj]
    {β : ℝ} (hβ : 0 < β)
    (hupper : ∀ u v, H.Adj u v → (H.degree u : ℝ) + H.degree v ≤ β) (v : W) :
    (H.degree v : ℝ) / β < 1 := by
  apply (div_lt_one hβ).mpr
  by_cases hz : H.degree v = 0
  · simpa [hz] using hβ
  · have hv : 0 < H.degree v := Nat.pos_of_ne_zero hz
    obtain ⟨u, hu⟩ := (H.degree_pos_iff_exists_adj v).mp hv
    have hdu : (0 : ℝ) < H.degree u := by exact_mod_cast hu.degree_pos_right
    have hh := hupper v u hu
    linarith

/-- Genuine finite graph-to-support bridge. The outside type is the complement
of an actual vertex cover, the center type is that cover, row degrees are full
H-degrees, and center degrees include all H-edges (even internal cover edges).
Thus the support lemmas do not assume their graph conclusions as hypotheses. -/
theorem supportData_of_graph_cover (H : SimpleGraph W) [DecidableRel H.Adj]
    (C : Set W) [DecidablePred (· ∈ C)] (hC : H.IsVertexCover C)
    {β : ℝ} (hβ : 0 < β)
    (hupper : ∀ u v, H.Adj u v → (H.degree u : ℝ) + H.degree v ≤ β) :
    SupportData
      (fun (s : {v : W // v ∉ C}) (c : {v : W // v ∈ C}) => H.Adj s.val c.val)
      β (fun s => (H.degree s.val : ℝ)/β) (fun c => (H.degree c.val : ℝ)) := by
  constructor
  · exact hβ
  · intro s
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hβ)
  · intro s
    exact normalized_degree_lt_one H hβ hupper s.val
  · intro s
    have hcard : (Finset.univ.filter fun c : {v : W // v ∈ C} => H.Adj s.val c.val).card =
        H.degree s.val := by
      rw [← H.card_neighborFinset_eq_degree]
      apply Finset.card_bij (fun c _ => c.val)
      · intro c hc
        exact (H.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hc).2
      · intro c hc d hd hcd
        exact Subtype.ext hcd
      · intro v hv
        have hadj := (H.mem_neighborFinset _ _).mp hv
        have hvc : v ∈ C := (hC hadj).resolve_left s.property
        refine ⟨⟨v, hvc⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩
    rw [hcard]
    field_simp
  · intro c
    let T : Finset {v : W // v ∉ C} := Finset.univ.filter fun s => H.Adj s.val c.val
    have hinj : Set.InjOn Subtype.val (T : Set {v : W // v ∉ C}) := by
      intro s hs t ht hst
      exact Subtype.ext hst
    have hsub : T.image Subtype.val ⊆ H.neighborFinset c.val := by
      intro v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
      have hadj := (Finset.mem_filter.mp hs).2
      exact (H.mem_neighborFinset _ _).mpr hadj.symm
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinj, H.card_neighborFinset_eq_degree] at hh
    exact_mod_cast hh
  · intro s c hadj
    have hh := hupper s.val c.val hadj
    have heq : β * ((H.degree s.val : ℝ)/β) = H.degree s.val := by field_simp
    rwa [heq]

end RandomOrderMatching.Analysis.Repair.Reference

#print axioms RandomOrderMatching.Analysis.Repair.Reference.normalized_degree_lt_one
#print axioms RandomOrderMatching.Analysis.Repair.Reference.supportData_of_graph_cover
