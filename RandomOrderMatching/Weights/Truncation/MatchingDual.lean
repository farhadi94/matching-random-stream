import RandomOrderMatching.Analysis.Repair.CoverRecovery
import RandomOrderMatching.Weights.Truncation.PriceMap

/-! Actual finite matching weak duality with odd-set prices, and cumulative
laminar-chain telescoping. Strong duality/uncrossing are not axiomatized. -/
open scoped BigOperators
namespace RandomOrderMatching.Weights.Truncation.MatchingDual
open RandomOrderMatching.Graph.CompletionKernel RandomOrderMatching.Analysis.Repair.CoverRecovery
open RandomOrderMatching.Weights.Truncation.PriceMap
variable {V : Type*} [DecidableEq V]

theorem occupied_card {M : Finset (Finset V)} (hM : IsMatching M) :
    (occupied M).card = 2*M.card := by
  rw [occupied, Finset.card_biUnion]
  · simp only [id_eq]
    rw [Finset.sum_congr rfl (fun e he => hM.1 e he)]
    simp [mul_comm]
  · intro e he f hf hne
    exact hM.2 e he f hf hne

def internal (M : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  M.filter (fun e => e ⊆ S)

/-- Actual matching edges internal to an odd set obey its blossom capacity. -/
theorem odd_internal_count {M : Finset (Finset V)} (hM : IsMatching M)
    (S : Finset V) (hodd : Odd S.card) :
    ((internal M S).card:ℝ) ≤ ((S.card:ℝ)-1)/2 := by
  have hm : IsMatching (internal M S) := matching_subset hM (Finset.filter_subset _ _)
  have hsub : occupied (internal M S) ⊆ S := by
    intro v hv
    obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp he).2 hv
  have hc := Finset.card_le_card hsub
  rw [occupied_card hm] at hc
  obtain ⟨r,hr⟩ := hodd
  have h : 2*(internal M S).card+1 ≤ S.card := by omega
  have hh : (2:ℝ)*((internal M S).card:ℝ)+1 ≤ (S.card:ℝ) := by exact_mod_cast h
  linarith

/-- Feasible vertex/odd-set prices bound any genuine matching. -/
theorem matching_weak_dual [Fintype V] {M : Finset (Finset V)} (hM : IsMatching M)
    (B : Finset (Finset V)) (y : V → ℝ) (z w : Finset V → ℝ)
    (hy : ∀ v, 0 ≤ y v) (hz : ∀ S ∈ B, 0 ≤ z S) (hodd : ∀ S ∈ B, Odd S.card)
    (hcover : ∀ e ∈ M, w e ≤ (∑ v ∈ e, y v) + ∑ S ∈ B, if e ⊆ S then z S else 0) :
    (∑ e ∈ M, w e) ≤ (∑ v, y v) + ∑ S ∈ B, (((S.card:ℝ)-1)/2)*z S := by
  classical
  have hv : (∑ e ∈ M, ∑ v ∈ e, y v) ≤ ∑ v, y v := by
    apply weighted_cover_bound hM y (fun e => ∑ v ∈ e, y v) (fun v _ => hy v)
    intro e he
    simp
  have hb : (∑ e ∈ M, ∑ S ∈ B, if e ⊆ S then z S else 0) ≤
      ∑ S ∈ B, (((S.card:ℝ)-1)/2)*z S := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro S hS
    have heq : (∑ e ∈ M, if e ⊆ S then z S else 0) = ((internal M S).card:ℝ)*z S := by
      simp [internal, ← Finset.sum_filter, Finset.sum_const]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (odd_internal_count hM S (hodd S hS)) (hz S hS)
  calc
    _ ≤ ∑ e ∈ M, ((∑ v ∈ e, y v) + ∑ S ∈ B, if e ⊆ S then z S else 0) :=
      Finset.sum_le_sum hcover
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

/-- Common edge-containing members of a laminar family are comparable.
This proves that one ancestor chain, rather than all blossoms, covers an edge. -/
theorem common_sets_comparable (B : Finset (Finset V))
    (hlam : ∀ A ∈ B, ∀ C ∈ B, A ⊆ C ∨ C ⊆ A ∨ Disjoint A C)
    {A C : Finset V} (hA : A ∈ B) (hC : C ∈ B) {u : V}
    (huA : u ∈ A) (huC : u ∈ C) : A ⊆ C ∨ C ⊆ A := by
  rcases hlam A hA C hC with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (Finset.disjoint_left.mp h huA huC)

noncomputable def cumulative (z : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, z i
lemma cumulative_step (z : ℕ → ℝ) (j : ℕ) : cumulative z (j+1) = cumulative z j + z j := by
  simp [cumulative, Finset.sum_range_succ]

theorem chain_increment_nonneg (z : ℕ → ℝ) (L U : ℝ) (j : ℕ) (hz : 0 ≤ z j) :
    0 ≤ trunc L U (cumulative z (j+1))-trunc L U (cumulative z j) := by
  have h := trunc_monotone L U (show cumulative z j ≤ cumulative z (j+1) by rw [cumulative_step]; linarith)
  linarith

/-- Parent differences telescope exactly for arbitrary depth, including zero. -/
theorem chain_telescope (z : ℕ → ℝ) (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U) (r : ℕ) :
    (∑ j ∈ Finset.range r,
      (trunc L U (cumulative z (j+1))-trunc L U (cumulative z j))) = trunc L U (cumulative z r) := by
  rw [Finset.sum_range_sub (fun j => trunc L U (cumulative z j))]
  simp [cumulative, trunc_zero hL hU]

/-- An actual two-endpoint constraint with any common ancestor chain remains covered. -/
theorem transformed_edge_cover (z : ℕ → ℝ) (L U a b w : ℝ)
    (hL : 0 ≤ L) (hU : 0 ≤ U) (r : ℕ) (hwL : L ≤ w) (hwU : w ≤ U)
    (hcover : w ≤ a+b+cumulative z r) :
    w ≤ trunc L U a + trunc L U b + ∑ j ∈ Finset.range r,
      (trunc L U (cumulative z (j+1))-trunc L U (cumulative z j)) := by
  rw [chain_telescope z L U hL hU r]
  exact three_price_cover hL hU hwL hwU hcover

/-- k-fold membership gives the exact objective double count for arbitrary weights. -/
theorem incidence_sum {E I : Type*} [DecidableEq E] [DecidableEq I]
    (M : Finset E) (T : Finset I) (mem : I → E → Prop) [DecidableRel mem]
    (k : ℕ) (w : E → ℝ) (hcount : ∀ e ∈ M, (T.filter (fun i => mem i e)).card = k) :
    (∑ i ∈ T, ∑ e ∈ M, if mem i e then w e else 0) = (k:ℝ)*∑ e ∈ M, w e := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_filter]
  simp [hcount e he]

end RandomOrderMatching.Weights.Truncation.MatchingDual
#print axioms RandomOrderMatching.Weights.Truncation.MatchingDual.odd_internal_count
#print axioms RandomOrderMatching.Weights.Truncation.MatchingDual.matching_weak_dual
#print axioms RandomOrderMatching.Weights.Truncation.MatchingDual.common_sets_comparable
#print axioms RandomOrderMatching.Weights.Truncation.MatchingDual.transformed_edge_cover
#print axioms RandomOrderMatching.Weights.Truncation.MatchingDual.incidence_sum
