import RandomOrderMatching.Weights.Reduction.GeometricCharging
import RandomOrderMatching.Unfolding.EndpointModel

/-! Exact loss from one omitted residue class and composition of local
matching approximation contracts with the proved ordered greedy decoder. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Weights.Reduction.Shifts
open RandomOrderMatching.Graph RandomOrderMatching.Weights.Reduction.Greedy
open RandomOrderMatching.Weights.Reduction.GeometricCharging
variable {V : Type*} [DecidableEq V]

def kept (M : Graph V) {q : ℕ} (drop : Edge V → Fin q) (s : Fin q) : Graph V := by
  classical
  exact M.filter (fun e => drop e ≠ s)

theorem shifted_sum (M : Graph V) (w : Edge V → ℝ) {q : ℕ}
    (drop : Edge V → Fin q) :
    (∑ s : Fin q, ∑ e ∈ kept M drop s, w e) = ((q:ℝ)-1)*(∑ e ∈ M, w e) := by
  classical
  simp only [kept, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hs : (∑ s : Fin q, if drop e ≠ s then w e else 0) + w e = (q:ℝ)*w e := by
    calc
      _ = (∑ s : Fin q, if drop e ≠ s then w e else 0) +
          (∑ s : Fin q, if drop e = s then w e else 0) := by simp
      _ = ∑ _s : Fin q, w e := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        by_cases h : drop e = s <;> simp [h]
      _ = _ := by simp
  linarith

theorem exists_good_shift (M : Graph V) (w : Edge V → ℝ) {q : ℕ}
    (hq : 0 < q) (drop : Edge V → Fin q) :
    ∃ s : Fin q, (((q:ℝ)-1)/(q:ℝ))*(∑ e ∈ M, w e) ≤
      ∑ e ∈ kept M drop s, w e := by
  classical
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hne : (Finset.univ : Finset (Fin q)).Nonempty :=
    ⟨⟨0,hq⟩,Finset.mem_univ _⟩
  obtain ⟨s,hs,hval⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ : Fin q => (((q:ℝ)-1)/(q:ℝ))*(∑ e ∈ M,w e))
    (g := fun s => ∑ e ∈ kept M drop s,w e) (by
      rw [shifted_sum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
      <;> ring_nf
      <;> exact le_rfl)
  exact ⟨s,hval⟩

theorem levels_disjoint (levels : ℕ → Graph V) (n : ℕ) (index : Edge V → ℕ)
    (hindex : ∀ i < n, ∀ e ∈ levels i, index e = i) :
    (Finset.range n : Set ℕ).PairwiseDisjoint levels := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  exact hij ((hindex i (Finset.mem_range.mp hi) e hei).symm.trans
    (hindex j (Finset.mem_range.mp hj) e hej))

/-- Local approximation hypotheses apply only to actual benchmark restrictions.
The global union bound is derived by disjoint-level double counting. -/
theorem local_approximation_assembly (M : Graph V) (levels : ℕ → Graph V)
    (n : ℕ) (index : Edge V → ℕ)
    (hindex : ∀ i < n, ∀ e ∈ levels i, index e = i)
    (hMindex : ∀ e ∈ M, index e < n) (w : Edge V → ℝ) (alpha : ℝ)
    (hlocal : ∀ i < n,
      alpha*(∑ e ∈ M.filter (fun e => index e = i),w e) ≤ ∑ e ∈ levels i,w e) :
    alpha*(∑ e ∈ M,w e) ≤ ∑ e ∈ (Finset.range n).biUnion levels,w e := by
  classical
  have hs := Finset.sum_le_sum (fun i hi => hlocal i (Finset.mem_range.mp hi))
  rw [← Finset.mul_sum] at hs
  have hmaps : ∀ e ∈ M,index e ∈ Finset.range n :=
    fun e he => Finset.mem_range.mpr (hMindex e he)
  rw [Finset.sum_fiberwise_of_maps_to hmaps w] at hs
  rw [Finset.sum_biUnion (levels_disjoint levels n index hindex)]
  exact hs

/-- A complete finite composition contract, with the greedy decoder explicit.
The only approximation premise is the local algorithm's per-band guarantee. -/
theorem local_to_greedy (M : Graph V) (levels : ℕ → Graph V) (n : ℕ)
    (index : Edge V → ℕ) (hindex : ∀ i < n, ∀ e ∈ levels i,index e = i)
    (hMindex : ∀ e ∈ M,index e < n) (hL : ∀ i,Matching (levels i))
    (w : Edge V → ℝ) {alpha r A B : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) (hB : 0 < B)
    (hweights : ∀ i < n,∀ e ∈ levels i,A*r^i ≤ w e ∧ w e ≤ A*r^i/(B*r))
    (hlocal : ∀ i < n,
      alpha*(∑ e ∈ M.filter (fun e => index e = i),w e) ≤ ∑ e ∈ levels i,w e) :
    (alpha/(1+2/(B*(1-r))))*(∑ e ∈ M,w e) ≤ ∑ e ∈ combine levels n,w e := by
  have hlow := local_approximation_assembly M levels n index hindex hMindex w alpha hlocal
  have hupp := separated_combine levels n index hindex hL w hr hr1 hA hB hweights
  have hp : 0 < 1+2/(B*(1-r)) := by positivity
  convert (show alpha*(∑ e ∈ M,w e)/(1+2/(B*(1-r))) ≤
      ∑ e ∈ combine levels n,w e from (div_le_iff₀ hp).mpr
        (by simpa only [mul_comm] using hlow.trans hupp)) using 1 <;> ring

end RandomOrderMatching.Weights.Reduction.Shifts

#print axioms RandomOrderMatching.Weights.Reduction.Shifts.exists_good_shift
#print axioms RandomOrderMatching.Weights.Reduction.Shifts.local_to_greedy
