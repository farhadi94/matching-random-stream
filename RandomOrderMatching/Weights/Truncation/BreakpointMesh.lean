import RandomOrderMatching.Weights.Truncation.Budget
import Mathlib.Data.Finset.Sort

/-! Existence of the finite breakpoint certificates and hence an unconditional
finite dyadic Lipschitz theorem. The construction sorts all breakpoints. -/
open scoped BigOperators
namespace RandomOrderMatching.Weights.Truncation.BreakpointMesh
open RandomOrderMatching.Weights.Truncation.PriceMap RandomOrderMatching.Weights.Truncation.DyadicIncrement
open RandomOrderMatching.Weights.Truncation.Budget

private theorem finite_partition (cuts : Finset ℝ) (a b : ℝ) (hab : a ≤ b) :
    ∃ m : ℕ, ∃ p : ℕ → ℝ, p 0 = a ∧ p m = b ∧
      (∀ j < m, p j ≤ p (j+1)) ∧
      (∀ j < m, ∀ c ∈ cuts, ¬ (p j < c ∧ c < p (j+1))) := by
  classical
  let S := insert a (insert b (cuts.filter (fun c => a ≤ c ∧ c ≤ b)))
  have ha : a ∈ S := by simp [S]
  have hb : b ∈ S := by simp [S]
  have hn : S.Nonempty := ⟨a,ha⟩
  have hc : 0 < S.card := Finset.card_pos.mpr hn
  have hbounds : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨_,hx⟩
    · exact ⟨le_rfl,hab⟩
    · exact ⟨hab,le_rfl⟩
    · exact hx
  let p : ℕ → ℝ := fun j => if h : j < S.card then S.orderEmbOfFin rfl ⟨j,h⟩ else b
  have hp (j : ℕ) (hj : j < S.card) : p j = S.orderEmbOfFin rfl ⟨j,hj⟩ := by simp [p,hj]
  have hfirst : p 0 = a := by
    rw [hp 0 hc, Finset.orderEmbOfFin_zero rfl hc]
    exact (Finset.min'_eq_iff _ _ a).mpr ⟨ha,fun x hx => (hbounds x hx).1⟩
  have hlast : p (S.card-1) = b := by
    rw [hp (S.card-1) (by omega), Finset.orderEmbOfFin_last rfl hc]
    exact (Finset.max'_eq_iff _ _ b).mpr ⟨hb,fun x hx => (hbounds x hx).2⟩
  refine ⟨S.card-1,p,hfirst,hlast,?_,?_⟩
  · intro j hj
    rw [hp j (by omega), hp (j+1) (by omega)]
    exact (S.orderEmbOfFin rfl).monotone (by change j ≤ j+1; omega)
  · intro j hj c hcc hcross
    have hj0 : j < S.card := by omega
    have hj1 : j+1 < S.card := by omega
    have hjmem : p j ∈ S := by rw [hp j hj0]; exact S.orderEmbOfFin_mem rfl _
    have hjmem' : p (j+1) ∈ S := by rw [hp (j+1) hj1]; exact S.orderEmbOfFin_mem rfl _
    have hcin : c ∈ S := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      exact ⟨hcc,⟨(hbounds (p j) hjmem).1.trans hcross.1.le,
        hcross.2.le.trans (hbounds (p (j+1)) hjmem').2⟩⟩
    let q : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨c,hcin⟩
    have hq : S.orderEmbOfFin rfl q = c := by
      have h := congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨c,hcin⟩)
      exact h
    have hleft : (⟨j,hj0⟩ : Fin S.card) < q := by
      apply (S.orderEmbOfFin rfl).lt_iff_lt.mp
      simpa [← hq, hp j hj0] using hcross.1
    have hright : q < (⟨j+1,hj1⟩ : Fin S.card) := by
      apply (S.orderEmbOfFin rfl).lt_iff_lt.mp
      simpa [← hq, hp (j+1) hj1] using hcross.2
    have : j < q.val := hleft
    have : q.val < j+1 := hright
    omega

private theorem piece_of_no_cross (L U a b : ℝ) (hab : a ≤ b)
    (h1 : ¬ (a < L/4 ∧ L/4 < b))
    (h2 : ¬ (a < L/2 ∧ L/2 < b))
    (h3 : ¬ (a < U-L/2 ∧ U-L/2 < b)) : Piece L U a b := by
  by_cases hb1 : b ≤ L/4
  · exact Or.inl hb1
  have ha1 : L/4 ≤ a := by by_contra h; exact h1 ⟨by linarith,by linarith⟩
  by_cases hb2 : b ≤ L/2
  · exact Or.inr (Or.inl ⟨ha1,hb2⟩)
  have ha2 : L/2 ≤ a := by by_contra h; exact h2 ⟨by linarith,by linarith⟩
  by_cases hb3 : b ≤ U-L/2
  · exact Or.inr (Or.inr (Or.inl ⟨ha2,hb3⟩))
  have ha3 : U-L/2 ≤ a := by by_contra h; exact h3 ⟨by linarith,by linarith⟩
  exact Or.inr (Or.inr (Or.inr ha3))

theorem mesh_exists (T : Finset ℤ) (k : ℕ) (a b : ℝ) (hab : a ≤ b) :
    Nonempty (Mesh T k a b) := by
  classical
  let cuts : Finset ℝ := T.biUnion (fun i => {lo i/4,lo i/2,up k i-lo i/2})
  obtain ⟨m,p,hfirst,hlast,hmono,hnocross⟩ := finite_partition cuts a b hab
  refine ⟨⟨m,p,hfirst,hlast,hmono,?_⟩⟩
  intro j hj i hi
  apply piece_of_no_cross _ _ _ _ (hmono j hj)
  · apply hnocross j hj
    exact Finset.mem_biUnion.mpr ⟨i,hi,by simp⟩
  · apply hnocross j hj
    exact Finset.mem_biUnion.mpr ⟨i,hi,by simp⟩
  · apply hnocross j hj
    exact Finset.mem_biUnion.mpr ⟨i,hi,by simp⟩

/-- Full finite dyadic increment bound: no supplied mesh, slopes or costs. -/
theorem dyadic_increment (T : Finset ℤ) (k : ℕ) (hk : 1 ≤ k) (a b : ℝ)
    (hab : a ≤ b) :
    0 ≤ (∑ i ∈ T, (trunc (lo i) (up k i) b-trunc (lo i) (up k i) a)) ∧
    (∑ i ∈ T, (trunc (lo i) (up k i) b-trunc (lo i) (up k i) a)) ≤
      ((k:ℝ)+5)*(b-a) := by
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact sub_nonneg.mpr (trunc_monotone _ _ hab)
  · exact interval_budget T k hk a b (Classical.choice (mesh_exists T k a b hab))

/-- Full cost bound with arbitrary nonnegative coefficients (odd-set or rank). -/
theorem dyadic_cost {C : Type*} [DecidableEq C]
    (S : Finset C) (T : Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (a b cost : C → ℝ) (hcost : ∀ c ∈ S, 0 ≤ cost c)
    (hab : ∀ c ∈ S, a c ≤ b c) :
    (∑ i ∈ T, ∑ c ∈ S, cost c *
      (trunc (lo i) (up k i) (b c)-trunc (lo i) (up k i) (a c))) ≤
      ((k:ℝ)+5) * ∑ c ∈ S, cost c*(b c-a c) := by
  exact weighted_interval_budget S T k hk a b cost hcost
    (fun c hc => Classical.choice (mesh_exists T k (a c) (b c) (hab c hc)))
end RandomOrderMatching.Weights.Truncation.BreakpointMesh
#print axioms RandomOrderMatching.Weights.Truncation.BreakpointMesh.mesh_exists
#print axioms RandomOrderMatching.Weights.Truncation.BreakpointMesh.dyadic_increment
#print axioms RandomOrderMatching.Weights.Truncation.BreakpointMesh.dyadic_cost
