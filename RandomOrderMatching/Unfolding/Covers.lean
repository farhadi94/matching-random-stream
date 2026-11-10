import RandomOrderMatching.Graph.BipartiteDual.Lattice

/-! Actual unfolding covers and arbitrary selected root-copy deletion bounds.
Strong duality for the auxiliary bipartite graph is a written classical input.
No bottom-prefix restriction is placed on the selected root copies. -/
open scoped BigOperators
namespace RandomOrderMatching.Unfolding.Covers
open RandomOrderMatching.Graph.BipartiteDual

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]

def CopyEdges (W : ℕ) (E : Set (L × R)) (w : L × R → ℕ) :
    Set ((L × Fin W) × (R × Fin W)) :=
  fun e => (e.1.1, e.2.1) ∈ E ∧ e.1.2.val + e.2.2.val + 1 = w (e.1.1, e.2.1)

def bottom (W : ℕ) (pL : L → ℕ) (pR : R → ℕ) : Potential (L × Fin W) (R × Fin W) :=
  ⟨fun u => if u.2.val < pL u.1 then 1 else 0,
   fun v => if v.2.val < pR v.1 then 1 else 0⟩

theorem bottom_covers (W : ℕ) (E : Set (L × R)) (w : L × R → ℕ)
    (pL : L → ℕ) (pR : R → ℕ)
    (h : ∀ e ∈ E, w e ≤ pL e.1 + pR e.2) :
    Feasible (CopyEdges W E w) (fun _ => 1) (bottom W pL pR) := by
  constructor
  · intro u; simp only [bottom]; split <;> norm_num
  · intro v; simp only [bottom]; split <;> norm_num
  · intro e he
    obtain ⟨he, hidx⟩ := he
    have hp := h (e.1.1, e.2.1) he
    change w (e.1.1, e.2.1) ≤ pL e.1.1 + pR e.2.1 at hp
    dsimp [bottom]
    split <;> split <;> try norm_num
    omega

theorem bottom_index_sum_le (W t : ℕ) :
    (∑ i : Fin W, if i.val < t then (1 : ℝ) else 0) ≤ t := by
  let S : Finset (Fin W) := Finset.univ.filter (fun i => i.val < t)
  have hi : Function.Injective (fun i : Fin W => i.val) := Fin.val_injective
  have hs : S.image (fun i => i.val) ⊆ Finset.range t := by
    intro x hx
    obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hiS).2
  have hc : S.card ≤ t := by
    have hh := Finset.card_le_card hs
    simpa [Finset.card_image_of_injective _ hi] using hh
  have hsum : (∑ i : Fin W, if i.val < t then (1 : ℝ) else 0) = (S.card : ℝ) := by
    simp [S, Finset.sum_filter]
  rw [hsum]
  exact_mod_cast hc

theorem bottom_cost_le (W : ℕ) (pL : L → ℕ) (pR : R → ℕ) :
    cost (bottom W pL pR) ≤ (∑ u, (pL u : ℝ)) + ∑ v, (pR v : ℝ) := by
  unfold cost bottom
  simp only [Fintype.sum_prod_type]
  exact add_le_add (Finset.sum_le_sum (fun u _ => bottom_index_sum_le W (pL u)))
    (Finset.sum_le_sum (fun v _ => bottom_index_sum_le W (pR v)))

/-- A mixed integral price constraint covers either the left copy in the
first cover or the right copy in the second cover, for every copy index. -/
theorem mixed_copy_cover (W : ℕ) (w : L × R → ℕ)
    (pL : L → ℕ) (pR : R → ℕ)
    (e : (L × Fin W) × (R × Fin W))
    (hidx : e.1.2.val + e.2.2.val + 1 = w (e.1.1, e.2.1))
    (hp : w (e.1.1, e.2.1) ≤ pL e.1.1 + pR e.2.1) :
    (1 : ℝ) ≤ (if e.1.2.val < pL e.1.1 then 1 else 0) +
      (if e.2.2.val < pR e.2.1 then 1 else 0) := by
  split <;> split <;> try norm_num
  omega

/-- Any subset of the antidiagonal copies of an original matching remains
an actual matching. The selected indices need not form intervals. -/
theorem copy_subset_matching (W : ℕ) (w : L × R → ℕ)
    (J : Finset (L × R)) (hJ : IsMatching J)
    (Rcopy : Finset ((L × Fin W) × (R × Fin W)))
    (hsub : ∀ e ∈ Rcopy, (e.1.1, e.2.1) ∈ J)
    (hidx : ∀ e ∈ Rcopy, e.1.2.val + e.2.2.val + 1 = w (e.1.1, e.2.1)) :
    IsMatching Rcopy := by
  constructor
  · intro e he f hf hh
    have ho : (e.1.1, e.2.1) = (f.1.1, f.2.1) :=
      hJ.1 (hsub e he) (hsub f hf) (congrArg (fun z : L × Fin W => z.1) hh)
    have heq := hidx e he
    have hfq := hidx f hf
    have hi := congrArg (fun z : L × Fin W => z.2.val) hh
    rw [ho] at heq
    apply Prod.ext hh
    have hR : e.2.1 = f.2.1 := congrArg (fun z : L × R => z.2) ho
    apply Prod.ext hR
    apply Fin.ext
    omega
  · intro e he f hf hh
    have ho : (e.1.1, e.2.1) = (f.1.1, f.2.1) :=
      hJ.2 (hsub e he) (hsub f hf) (congrArg (fun z : R × Fin W => z.1) hh)
    have heq := hidx e he
    have hfq := hidx f hf
    have hi := congrArg (fun z : R × Fin W => z.2.val) hh
    rw [ho] at heq
    apply Prod.ext _ hh
    have hL : e.1.1 = f.1.1 := congrArg (fun z : L × R => z.1) ho
    apply Prod.ext hL
    apply Fin.ext
    omega

/-- The two deletion matchings may be arbitrary subgraphs of the full
unfolding; Rcopy may be any matching of selected proposed-edge copies. -/
theorem arbitrary_copy_deletion_bound
    (W : ℕ) (E : Set (L × R)) (wA wJ : L × R → ℕ)
    (p1L p2L : L → ℕ) (p1R p2R : R → ℕ)
    (h1 : ∀ e ∈ E, wA e ≤ p1L e.1 + p1R e.2)
    (h2 : ∀ e ∈ E, wA e ≤ p2L e.1 + p2R e.2)
    (M1 M2 Rcopy : Finset ((L × Fin W) × (R × Fin W)))
    (hm1 : IsMatching M1) (hm2 : IsMatching M2) (hr : IsMatching Rcopy)
    (hs1 : ∀ e ∈ M1, e ∈ CopyEdges W E wA)
    (hs2 : ∀ e ∈ M2, e ∈ CopyEdges W E wA)
    (hd1 : Disjoint (M1.image Prod.fst) (Rcopy.image Prod.fst))
    (hd2 : Disjoint (M2.image Prod.snd) (Rcopy.image Prod.snd))
    (hidx : ∀ e ∈ Rcopy, e.1.2.val + e.2.2.val + 1 = wJ (e.1.1, e.2.1))
    (hmix : ∀ e ∈ Rcopy, wJ (e.1.1, e.2.1) ≤ p1L e.1.1 + p2R e.2.1) :
    (M1.card : ℝ) + M2.card + Rcopy.card ≤
      ((∑ u, (p1L u : ℝ)) + ∑ v, (p1R v : ℝ)) +
      ((∑ u, (p2L u : ℝ)) + ∑ v, (p2R v : ℝ)) := by
  have hl := deletion_left_bound (bottom_covers W E wA p1L p1R h1)
    hm1 hr hs1 hd1
  have hr' := deletion_right_bound (bottom_covers W E wA p2L p2R h2)
    hm2 hr hs2 hd2
  have hj : (Rcopy.card : ℝ) ≤
      (∑ e ∈ Rcopy, (bottom W p1L p1R).left e.1) +
      (∑ e ∈ Rcopy, (bottom W p2L p2R).right e.2) := by
    have hs := Finset.sum_le_sum (fun e he => mixed_copy_cover W wJ p1L p2R e
      (hidx e he) (hmix e he))
    simpa [bottom, Finset.sum_add_distrib] using hs
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hl hr'
  have hc1 := bottom_cost_le W p1L p1R
  have hc2 := bottom_cost_le W p2L p2R
  linarith

end RandomOrderMatching.Unfolding.Covers
#print axioms RandomOrderMatching.Unfolding.Covers.bottom_covers
#print axioms RandomOrderMatching.Unfolding.Covers.bottom_cost_le
#print axioms RandomOrderMatching.Unfolding.Covers.copy_subset_matching
#print axioms RandomOrderMatching.Unfolding.Covers.arbitrary_copy_deletion_bound
