import RandomOrderMatching.Weights.Reduction.Retirement

/-! The actual greedy union of an ordered list of matchings. Edges rejected
from a level are blocked by an edge of an earlier level. The two-per-level
charge is proved from vertex-disjointness, not assumed as a packing oracle. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Weights.Reduction.Greedy
open RandomOrderMatching.Graph
variable {V : Type*} [DecidableEq V]

def freeEdges (A B : Graph V) : Graph V := by
  classical
  exact B.filter (fun e => Disjoint e.val (covered A))

def addLevel (A B : Graph V) : Graph V := A ∪ freeEdges A B

def combine (levels : ℕ → Graph V) : ℕ → Graph V :=
  Nat.rec ∅ (fun i A => addLevel A (levels i))

theorem freeEdges_subset (A B : Graph V) : freeEdges A B ⊆ B :=
  Finset.filter_subset _ _

theorem addLevel_matching {A B : Graph V} (hA : Matching A) (hB : Matching B) :
    Matching (addLevel A B) := by
  intro e he f hf hef
  rcases Finset.mem_union.mp he with he | he
  · rcases Finset.mem_union.mp hf with hf | hf
    · exact hA he hf hef
    · have hd := (Finset.mem_filter.mp hf).2
      exact (hd.mono_right (fun v hv => mem_covered.mpr ⟨e, he, hv⟩)).symm
  · rcases Finset.mem_union.mp hf with hf | hf
    · have hd := (Finset.mem_filter.mp he).2
      exact hd.mono_right (fun v hv => mem_covered.mpr ⟨f, hf, hv⟩)
    · exact hB ((freeEdges_subset A B) he) ((freeEdges_subset A B) hf) hef

theorem combine_matching (levels : ℕ → Graph V) (hM : ∀ i, Matching (levels i))
    (n : ℕ) : Matching (combine levels n) := by
  induction n with
  | zero => simp [combine, Matching]
  | succ n ih => exact addLevel_matching ih (hM n)

theorem combine_step (levels : ℕ → Graph V) (n : ℕ) :
    combine levels n ⊆ combine levels (n+1) := Finset.subset_union_left

theorem combine_mono (levels : ℕ → Graph V) {m n : ℕ} (hmn : m ≤ n) :
    combine levels m ⊆ combine levels n := by
  exact monotone_nat_of_le_succ (combine_step levels) hmn

/-- A stored edge came from an actual earlier input level. -/
theorem combine_origin (levels : ℕ → Graph V) {n : ℕ} {e : Edge V}
    (he : e ∈ combine levels n) : ∃ j < n, e ∈ levels j := by
  induction n with
  | zero => simp [combine] at he
  | succ n ih =>
    change e ∈ combine levels n ∪ freeEdges (combine levels n) (levels n) at he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨j,hj,he⟩ := ih he
      exact ⟨j, by omega, he⟩
    · exact ⟨n, Nat.lt_succ_self n, freeEdges_subset _ _ he⟩

theorem combine_subset_union (levels : ℕ → Graph V) (n : ℕ) :
    combine levels n ⊆ (Finset.range n).biUnion levels := by
  intro e he
  obtain ⟨j,hj,he⟩ := combine_origin levels he
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, he⟩

/-- Every rejected edge has a retained blocker from a strictly earlier level. -/
theorem rejected_blocker (levels : ℕ → Graph V) {i n : ℕ} (hin : i < n)
    {e : Edge V} (he : e ∈ levels i) (hnot : e ∉ combine levels n) :
    ∃ f ∈ combine levels n, ∃ j < i, f ∈ levels j ∧ ¬ Disjoint e.val f.val := by
  classical
  have hnotstep : e ∉ combine levels (i+1) :=
    fun h => hnot (combine_mono levels (Nat.succ_le_iff.mpr hin) h)
  have hnfree : e ∉ freeEdges (combine levels i) (levels i) :=
    fun h => hnotstep (Finset.mem_union_right _ h)
  have hnd : ¬ Disjoint e.val (covered (combine levels i)) := by
    intro hd
    exact hnfree (Finset.mem_filter.mpr ⟨he,hd⟩)
  obtain ⟨v,hve,hvcovered⟩ := Finset.not_disjoint_iff.mp hnd
  obtain ⟨f,hf,hvf⟩ := mem_covered.mp hvcovered
  obtain ⟨j,hj,hfj⟩ := combine_origin levels hf
  refine ⟨f, combine_mono levels (Nat.le_of_lt hin) hf, j, hj, hfj, ?_⟩
  exact Finset.not_disjoint_iff.mpr ⟨v,hve,hvf⟩

/-- At most two edges of a matching can meet one two-endpoint edge. -/
theorem meeting_count (M : Graph V) (hM : Matching M) (e : Edge V) :
    (M.filter (fun f => ¬ Disjoint f.val e.val)).card ≤ 2 := by
  classical
  have hm := matching_mono hM (Finset.filter_subset (fun f => ¬ Disjoint f.val e.val) M)
  have hc := matching_le_cover hm (S := e.val) (by
    intro f hf
    obtain ⟨v,hvf,hve⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hf).2
    exact ⟨v, Finset.mem_inter.mpr ⟨hvf,hve⟩⟩)
  simpa [e.property] using hc

/-- Any subset of one input matching charged to an incident blocker has
cardinality at most two, irrespective of the charge-selection rule. -/
theorem charge_count (M F : Graph V) (hM : Matching M) (hFM : F ⊆ M)
    (e : Edge V) (hmeet : ∀ f ∈ F, ¬ Disjoint f.val e.val) : F.card ≤ 2 := by
  apply le_trans (Finset.card_le_card (t := M.filter (fun f => ¬ Disjoint f.val e.val)) ?_)
    (meeting_count M hM e)
  intro f hf
  exact Finset.mem_filter.mpr ⟨hFM hf,hmeet f hf⟩

theorem charge_weight (M F : Graph V) (hM : Matching M) (hFM : F ⊆ M)
    (e : Edge V) (hmeet : ∀ f ∈ F, ¬ Disjoint f.val e.val)
    (w : Edge V → ℝ) {u : ℝ} (hu : 0 ≤ u) (hw : ∀ f ∈ F, w f ≤ u) :
    (∑ f ∈ F, w f) ≤ 2*u := by
  have hc : (F.card:ℝ) ≤ 2 := by exact_mod_cast charge_count M F hM hFM e hmeet
  calc
    _ ≤ ∑ _f ∈ F, u := Finset.sum_le_sum hw
    _ = (F.card:ℝ)*u := by simp
    _ ≤ 2*u := mul_le_mul_of_nonneg_right hc hu

end RandomOrderMatching.Weights.Reduction.Greedy

#print axioms RandomOrderMatching.Weights.Reduction.Greedy.combine_matching
#print axioms RandomOrderMatching.Weights.Reduction.Greedy.rejected_blocker
#print axioms RandomOrderMatching.Weights.Reduction.Greedy.charge_weight
