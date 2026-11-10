import RandomOrderMatching.Graph.CompletionKernel
import Mathlib.Tactic

/-! Actual finite matching recovery from a cover outside a reserved matching.
The graph may be nonbipartite. No optimum/recovery conclusion is assumed. -/
open scoped BigOperators
namespace RandomOrderMatching.Analysis.Repair.CoverRecovery
open RandomOrderMatching.Graph.CompletionKernel

variable {V : Type*} [DecidableEq V]

lemma matching_subset {M N : Finset (Finset V)} (hM : IsMatching M) (hNM : N ⊆ M) :
    IsMatching N :=
  ⟨fun e he => hM.1 e (hNM he),
   fun e he f hf hne => hM.2 e (hNM he) f (hNM hf) hne⟩

theorem matching_card_le_cover {M : Finset (Finset V)} {C : Finset V}
    (hM : IsMatching M) (hC : ∀ e ∈ M, ∃ v ∈ e, v ∈ C) :
    M.card ≤ C.card := by
  classical
  by_cases hn : Nonempty V
  · haveI := hn
    choose f hfedge hfcover using hC
    let g : Finset V → V := fun e => if he : e ∈ M then f e he else Classical.arbitrary V
    apply Finset.card_le_card_of_injOn g
    · intro e he
      change e ∈ M at he
      simpa [g, he] using hfcover e he
    · intro e he f' hf' heq
      change e ∈ M at he
      change f' ∈ M at hf'
      by_contra hne
      have he1 : g e ∈ e := by simpa [g, he] using hfedge e he
      have he2 : g f' ∈ f' := by simpa [g, hf'] using hfedge f' hf'
      exact (Finset.disjoint_left.mp (hM.2 e he f' hf' hne)) he1 (heq ▸ he2)
  · have hzero : M = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨v, _, _⟩ := hC e he
      exact hn ⟨v⟩
    simp [hzero]

lemma matching_union {M N : Finset (Finset V)} (hM : IsMatching M)
    (hN : IsMatching N) (hdisj : Disjoint (occupied M) (occupied N)) :
    IsMatching (M ∪ N) := by
  constructor
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hM.1 e he
    · exact hN.1 e he
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact hM.2 e he f hf hne
    · apply Finset.disjoint_left.mpr
      intro v hv hv'
      exact Finset.disjoint_left.mp hdisj
        (Finset.mem_biUnion.mpr ⟨e, he, hv⟩)
        (Finset.mem_biUnion.mpr ⟨f, hf, hv'⟩)
    · apply Finset.disjoint_left.mpr
      intro v hv hv'
      exact Finset.disjoint_left.mp hdisj
        (Finset.mem_biUnion.mpr ⟨f, hf, hv'⟩)
        (Finset.mem_biUnion.mpr ⟨e, he, hv⟩)
    · exact hN.2 e he f hf hne

lemma matching_edges_disjoint {M N : Finset (Finset V)} (hM : IsMatching M)
    (hdisj : Disjoint (occupied M) (occupied N)) : Disjoint M N := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  have hc := hM.1 e he
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < e.card)
  exact Finset.disjoint_left.mp hdisj
    (Finset.mem_biUnion.mpr ⟨e, he, hv⟩)
    (Finset.mem_biUnion.mpr ⟨e, he', hv⟩)

/-- Every matching uses at most `|C|` edges outside the reserved matching `F`. -/
theorem cover_deficit {G F A M : Finset (Finset V)} {C : Finset V}
    (hM : IsMatching M) (hMA : M ⊆ A) (hAG : A ⊆ G)
    (hcover : ∀ e ∈ G, e ∉ F → ∃ v ∈ e, v ∈ C) :
    M.card + ((F ∩ A) \ M).card ≤ C.card + (F ∩ A).card := by
  have houtside : (M \ F).card ≤ C.card :=
    matching_card_le_cover (matching_subset hM Finset.sdiff_subset)
      (by
        intro e he
        exact hcover e (hAG (hMA (Finset.mem_sdiff.mp he).1))
          (Finset.mem_sdiff.mp he).2)
  have hparts := Finset.card_sdiff_add_card_inter M F
  have hparts' := Finset.card_sdiff_add_card_inter (F ∩ A) M
  have hi : (F ∩ A) ∩ M = M ∩ F := by
    ext e
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hF, _⟩, hM⟩
      exact ⟨hM, hF⟩
    · rintro ⟨hM, hF⟩
      exact ⟨⟨hF, hMA hM⟩, hM⟩
  rw [hi] at hparts'
  omega

/-- Construct the output matching itself. Its exact loss is the omitted Alice
part of `F`; the preceding theorem bounds this loss by the cover deficit. -/
theorem recovery_witness {F J A B M : Finset (Finset V)}
    (hF : IsMatching F) (hJ : IsMatching J)
    (hJF : Disjoint (occupied J) (occupied F))
    (hpart : F ⊆ A ∪ B) :
    ∃ Q : Finset (Finset V), IsMatching Q ∧ Q ⊆ J ∪ B ∪ M ∧
      Q.card + ((F ∩ A) \ M).card = J.card + F.card := by
  let D := (F ∩ A) \ M
  let R := F \ D
  have hRF : R ⊆ F := Finset.sdiff_subset
  have hJR : Disjoint (occupied J) (occupied R) := by
    apply hJF.mono_right
    intro v hv
    obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨e, hRF he, hv⟩
  refine ⟨J ∪ R, matching_union hJ (matching_subset hF hRF) hJR, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
    · have heF := hRF he
      have heD := (Finset.mem_sdiff.mp he).2
      by_cases heM : e ∈ M
      · exact Finset.mem_union_right _ heM
      · have heB : e ∈ B := by
          rcases Finset.mem_union.mp (hpart heF) with heA | heB
          · exact False.elim (heD (Finset.mem_sdiff.mpr
              ⟨Finset.mem_inter.mpr ⟨heF, heA⟩, heM⟩))
          · exact heB
        exact Finset.mem_union_left _ (Finset.mem_union_right _ heB)
  · rw [Finset.card_union_of_disjoint (matching_edges_disjoint hJ hJR)]
    have hDF : D ⊆ F := fun e he => (Finset.mem_inter.mp (Finset.mem_sdiff.mp he).1).1
    have hcard := Finset.card_sdiff_add_card_eq_card hDF
    change J.card + (F \ D).card + D.card = J.card + F.card
    omega

/-- Prices supported on C cover all non-reserved edges. Summing over a genuine
matching spends each vertex price at most once; no bipartiteness is needed. -/
theorem weighted_cover_bound {M : Finset (Finset V)} {C : Finset V}
    (hM : IsMatching M) (p : V → ℝ) (w : Finset V → ℝ)
    (hp : ∀ v ∈ C, 0 ≤ p v)
    (hedge : ∀ e ∈ M, w e ≤ ∑ v ∈ e ∩ C, p v) :
    (∑ e ∈ M, w e) ≤ ∑ v ∈ C, p v := by
  calc
    (∑ e ∈ M, w e) ≤ ∑ e ∈ M, ∑ v ∈ e ∩ C, p v := Finset.sum_le_sum hedge
    _ = ∑ v ∈ M.biUnion (fun e => e ∩ C), p v := by
      symm
      apply Finset.sum_biUnion
      intro e he f hf hne
      exact (hM.2 e he f hf hne).mono Finset.inter_subset_left Finset.inter_subset_left
    _ ≤ ∑ v ∈ C, p v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hv
        exact (Finset.mem_inter.mp he).2
      · intro v hv _
        exact hp v hv

theorem weighted_cover_deficit {G F A M : Finset (Finset V)} {C : Finset V}
    (hM : IsMatching M) (hMA : M ⊆ A) (hAG : A ⊆ G)
    (p : V → ℝ) (w : Finset V → ℝ) (hp : ∀ v ∈ C, 0 ≤ p v)
    (hedge : ∀ e ∈ G, e ∉ F → w e ≤ ∑ v ∈ e ∩ C, p v) :
    (∑ e ∈ M, w e) + (∑ e ∈ (F ∩ A) \ M, w e) ≤
      (∑ v ∈ C, p v) + ∑ e ∈ F ∩ A, w e := by
  have hout := weighted_cover_bound (matching_subset hM (N := M \ F) Finset.sdiff_subset)
    p w hp (by
      intro e he
      exact hedge e (hAG (hMA (Finset.mem_sdiff.mp he).1)) (Finset.mem_sdiff.mp he).2)
  have hparts := Finset.sum_sdiff (Finset.inter_subset_left : M ∩ F ⊆ M) (f := w)
  have hparts' := Finset.sum_sdiff (Finset.inter_subset_left : (F ∩ A) ∩ M ⊆ F ∩ A) (f := w)
  have hi : (F ∩ A) ∩ M = M ∩ F := by
    ext e
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hF, _⟩, hM⟩
      exact ⟨hM, hF⟩
    · rintro ⟨hM, hF⟩
      exact ⟨⟨hF, hMA hM⟩, hM⟩
  have hd : M \ (M ∩ F) = M \ F := by ext e; simp
  have hd' : (F ∩ A) \ ((F ∩ A) ∩ M) = (F ∩ A) \ M := by ext e; simp; tauto
  rw [hd] at hparts
  rw [hd', hi] at hparts'
  linarith

#print axioms cover_deficit
#print axioms recovery_witness
#print axioms weighted_cover_deficit

/-- The EDCS degree-balance condition on the rectangular cross scaffold. -/
theorem rectangular_degree_balance (a b c lam : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 - lam ≤ a / (a+b) + c / (b+c)) :
    b^2 - lam * (a+b) * (b+c) ≤ a*c := by
  have hab : 0 < a+b := by linarith
  have hbc : 0 < b+c := by linarith
  have heq : a / (a+b) + c / (b+c) - (1-lam) =
      (a*c-b^2+lam*(a+b)*(b+c))/((a+b)*(b+c)) := by
    field_simp
    ring
  have hdiv : 0 ≤ (a*c-b^2+lam*(a+b)*(b+c))/((a+b)*(b+c)) := by
    rw [← heq]
    linarith
  have := (le_div_iff₀ (mul_pos hab hbc)).mp hdiv
  linarith

private theorem mixed_rectangle (a c : ℝ) (ha : 1 ≤ a)
    (hc : 0 ≤ c) (hac : 1 ≤ a*c) :
    7 * min 1 (a-1) ≤ 2*(a+1+c) := by
  have hapos : 0 < a := by linarith
  by_cases htwo : a ≤ 2
  · rw [min_eq_right (by linarith : a-1 ≤ 1)]
    have hp : 0 ≤ (5*a+1)*(2-a) := mul_nonneg (by linarith) (by linarith)
    have hm : a*(5*a-9-2*c) ≤ 0 := by nlinarith
    have hz : 5*a-9-2*c ≤ 0 := by
      by_contra hh
      have := mul_pos hapos (lt_of_not_ge hh)
      linarith
    linarith
  · rw [min_eq_left (by linarith : 1 ≤ a-1)]
    have hp : 0 ≤ (2*a-1)*(a-2) := mul_nonneg (by linarith) (by linarith)
    have hm : 0 ≤ a*(2*a+2*c-5) := by nlinarith
    have hz := (mul_nonneg_iff_of_pos_left hapos).mp hm
    linarith

/-- Sharp normalized rectangular loss inequality; equality occurs at (2,1/2). -/
theorem rectangular_six_sevenths (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hac : 1 ≤ a*c) :
    7 * min 1 (max 0 (a-1) + max 0 (c-1)) ≤ 2*(a+1+c) := by
  by_cases ha1 : 1 ≤ a
  · rw [max_eq_right (by linarith : 0 ≤ a-1)]
    by_cases hc1 : 1 ≤ c
    · rw [max_eq_right (by linarith : 0 ≤ c-1)]
      by_cases hsum : a+c ≤ 3
      · rw [min_eq_right (by linarith : a-1+(c-1) ≤ 1)]
        linarith
      · rw [min_eq_left (by linarith : 1 ≤ a-1+(c-1))]
        linarith
    · rw [max_eq_left (by linarith : c-1 ≤ 0), add_zero]
      exact mixed_rectangle a c ha1 hc hac
  · rw [max_eq_left (by linarith : a-1 ≤ 0), zero_add]
    by_cases hc1 : 1 ≤ c
    · rw [max_eq_right (by linarith : 0 ≤ c-1)]
      have h := mixed_rectangle c a hc1 ha (by nlinarith)
      linarith
    · rw [max_eq_left (by linarith : c-1 ≤ 0)]
      norm_num
      linarith

#print axioms rectangular_degree_balance
#print axioms rectangular_six_sevenths
end RandomOrderMatching.Analysis.Repair.CoverRecovery
