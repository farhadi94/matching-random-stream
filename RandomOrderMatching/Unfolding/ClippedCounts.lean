import RandomOrderMatching.Unfolding.Covers
import RandomOrderMatching.Unfolding.IntegralDuality

/-! Actual antidiagonal copies and clipped uncovered mass. Optimal price
existence is proved in RandomOrderMatching.Unfolding.IntegralDuality; this module proves the local
copy-counting/deletion bridge for any such prices. -/
open scoped BigOperators
noncomputable section
namespace RandomOrderMatching.Unfolding
open RandomOrderMatching.Graph.BipartiteDual RandomOrderMatching.Unfolding.Covers
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def parent {W : ℕ} (e : (L × Fin W) × (R × Fin W)) : L × R := (e.1.1,e.2.1)

def rootFiber {W : ℕ} (S : Finset ((L × Fin W) × (R × Fin W))) (e : L × R) :=
  S.filter (fun f => parent f = e)

def missed {W : ℕ} (S : Finset ((L × Fin W) × (R × Fin W)))
    (p : L → ℕ) (q : R → ℕ) :=
  S.filter (fun f => p f.1.1 ≤ f.1.2.val ∧ q f.2.1 ≤ f.2.2.val)

omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in
/-- Every missed copy of one original edge injects into a deficit-sized
integer interval, even when the selected copy set has arbitrary gaps. -/
theorem missed_single_card_le (W : ℕ) (S : Finset ((L × Fin W) × (R × Fin W)))
    (e : L × R) (w p q d : ℕ)
    (hp : ∀ f ∈ S, parent f = e)
    (hi : ∀ f ∈ S, f.1.2.val + f.2.2.val + 1 = w)
    (hm : ∀ f ∈ S, p ≤ f.1.2.val ∧ q ≤ f.2.2.val)
    (hprice : w ≤ p+q+d) : S.card ≤ d := by
  classical
  let index : ((L × Fin W) × (R × Fin W)) → ℕ := fun f => f.1.2.val-p
  have hinj : Set.InjOn index (S : Set _) := by
    intro f hf g hg heq
    have hfP := hp f hf
    have hgP := hp g hg
    have hfI := hi f hf
    have hgI := hi g hg
    have hfM := hm f hf
    have hgM := hm g hg
    have hil : f.1.2.val = g.1.2.val := by dsimp [index] at heq; omega
    have hir : f.2.2.val = g.2.2.val := by omega
    have hpar : parent f = parent g := hfP.trans hgP.symm
    have hL : f.1.1 = g.1.1 := congrArg (fun z : L × R => z.1) hpar
    have hR : f.2.1 = g.2.1 := congrArg (fun z : L × R => z.2) hpar
    exact Prod.ext (Prod.ext hL (Fin.ext hil)) (Prod.ext hR (Fin.ext hir))
  have hsub : S.image index ⊆ Finset.range d := by
    intro z hz
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_range.mpr
    have hI := hi f hf
    have hM := hm f hf
    dsimp [index]
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj,Finset.card_range] at hc
  exact hc

omit [Fintype L] [Fintype R] in
theorem missed_fiber_card_le (W : ℕ) (S : Finset ((L × Fin W) × (R × Fin W)))
    (w : L × R → ℕ) (p : L → ℕ) (q : R → ℕ) (d : L × R → ℕ)
    (e : L × R) (hi : ∀ f ∈ S, f.1.2.val + f.2.2.val + 1 = w (parent f))
    (hprice : w e ≤ p e.1 + q e.2 + d e) :
    (rootFiber (missed S p q) e).card ≤ min (rootFiber S e).card (d e) := by
  apply le_min
  · apply Finset.card_le_card
    intro f hf
    obtain ⟨hf,hpar⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1,hpar⟩
  · apply missed_single_card_le W _ e (w e) (p e.1) (q e.2) (d e)
    · intro f hf; exact (Finset.mem_filter.mp hf).2
    · intro f hf
      obtain ⟨hf,hpar⟩ := Finset.mem_filter.mp hf
      simpa [hpar] using hi f (Finset.mem_filter.mp hf).1
    · intro f hf
      obtain ⟨hf,hpar⟩ := Finset.mem_filter.mp hf
      have h := (Finset.mem_filter.mp hf).2
      have hL := congrArg Prod.fst hpar
      have hR := congrArg Prod.snd hpar
      dsimp [parent] at hL hR
      simpa [hL,hR] using h
    · exact hprice

theorem missed_card_le_clipped (W : ℕ) (S : Finset ((L × Fin W) × (R × Fin W)))
    (J : Finset (L × R)) (w : L × R → ℕ) (p : L → ℕ) (q : R → ℕ)
    (d : L × R → ℕ)
    (hsub : ∀ f ∈ S, parent f ∈ J)
    (hi : ∀ f ∈ S, f.1.2.val + f.2.2.val + 1 = w (parent f))
    (hprice : ∀ e ∈ J, w e ≤ p e.1 + q e.2 + d e) :
    (missed S p q).card ≤ ∑ e ∈ J, min (rootFiber S e).card (d e) := by
  have hmaps : ∀ f ∈ missed S p q, parent f ∈ J := by
    intro f hf; exact hsub f (Finset.mem_filter.mp hf).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_le_sum
  intro e he
  exact missed_fiber_card_le W S w p q d e hi (hprice e he)

/-- Actual two-deletion matching charge with a per-original clipped deficit.
The hypotheses describe feasible price vectors and graph containments, not
the target inequality. The sharp-static-to-price step is separate. -/
theorem clipped_copy_deletion_bound
    (W : ℕ) (E : Set (L × R)) (J : Finset (L × R)) (wA wJ d : L × R → ℕ)
    (p1L p2L : L → ℕ) (p1R p2R : R → ℕ)
    (h1 : ∀ e ∈ E, wA e ≤ p1L e.1 + p1R e.2)
    (h2 : ∀ e ∈ E, wA e ≤ p2L e.1 + p2R e.2)
    (M1 M2 S : Finset ((L × Fin W) × (R × Fin W)))
    (hm1 : IsMatching M1) (hm2 : IsMatching M2) (hJ : IsMatching J)
    (hs1 : ∀ e ∈ M1, e ∈ CopyEdges W E wA)
    (hs2 : ∀ e ∈ M2, e ∈ CopyEdges W E wA)
    (hsub : ∀ e ∈ S, parent e ∈ J)
    (hd1 : Disjoint (M1.image Prod.fst) (S.image Prod.fst))
    (hd2 : Disjoint (M2.image Prod.snd) (S.image Prod.snd))
    (hidx : ∀ e ∈ S, e.1.2.val + e.2.2.val + 1 = wJ (parent e))
    (hmix : ∀ e ∈ J, wJ e ≤ p1L e.1 + p2R e.2 + d e) :
    (M1.card : ℝ) + M2.card + S.card ≤
      ((∑ u, (p1L u : ℝ)) + ∑ v, (p1R v : ℝ)) +
      ((∑ u, (p2L u : ℝ)) + ∑ v, (p2R v : ℝ)) +
      (∑ e ∈ J, (min (rootFiber S e).card (d e) : ℝ)) := by
  have hr : IsMatching S := copy_subset_matching W wJ J hJ S hsub hidx
  have hl := deletion_left_bound (bottom_covers W E wA p1L p1R h1) hm1 hr hs1 hd1
  have hr' := deletion_right_bound (bottom_covers W E wA p2L p2R h2) hm2 hr hs2 hd2
  have hc1 := bottom_cost_le W p1L p1R
  have hc2 := bottom_cost_le W p2L p2R
  have hm := missed_card_le_clipped W S J wJ p1L p2R d hsub hidx hmix
  have hmr : ((missed S p1L p2R).card : ℝ) ≤
      ∑ e ∈ J, (min (rootFiber S e).card (d e) : ℝ) := by exact_mod_cast hm
  have hpoint (e : (L × Fin W) × (R × Fin W)) (_he : e ∈ S) :
      (1 : ℝ) ≤ (bottom W p1L p1R).left e.1 +
        (bottom W p2L p2R).right e.2 +
        (if p1L e.1.1 ≤ e.1.2.val ∧ p2R e.2.1 ≤ e.2.2.val then 1 else 0) := by
    simp only [bottom]
    split_ifs <;> norm_num at *
    omega
  have hsum := Finset.sum_le_sum hpoint
  have hmiss : (∑ e ∈ S, if p1L e.1.1 ≤ e.1.2.val ∧ p2R e.2.1 ≤ e.2.2.val
      then (1 : ℝ) else 0) = (missed S p1L p2R).card := by
    simp [missed]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hmiss] at hsum
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hl hr' hsum
  linarith

end RandomOrderMatching.Unfolding
#print axioms RandomOrderMatching.Unfolding.missed_card_le_clipped
#print axioms RandomOrderMatching.Unfolding.clipped_copy_deletion_bound
