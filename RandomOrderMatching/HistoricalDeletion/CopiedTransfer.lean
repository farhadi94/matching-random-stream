import RandomOrderMatching.HistoricalDeletion.CutEncoding
import RandomOrderMatching.Unfolding.TwoLayerPrices

/-! Historical copied transfer for an ARBITRARY crossing proposal graph.
Only the selected copied edges must be a matching; original parents may
overlap. The main theorem constructs the historical and dual witnesses. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace RandomOrderMatching.HistoricalDeletion.CopiedTransfer
open RandomOrderMatching.Graph.BipartiteDual RandomOrderMatching.Unfolding
open RandomOrderMatching.Unfolding.Covers

section AbstractBipartite
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem clipped_charge_of_copy_matching
    (W : ℕ) (E : Set (L × R)) (P : Finset (L × R)) (wA wP d : L × R → ℕ)
    (p1L p2L : L → ℕ) (p1R p2R : R → ℕ)
    (h1 : ∀ e ∈ E, wA e ≤ p1L e.1 + p1R e.2)
    (h2 : ∀ e ∈ E, wA e ≤ p2L e.1 + p2R e.2)
    (C1 C2 S : Finset ((L × Fin W) × (R × Fin W)))
    (hc1 : IsMatching C1) (hc2 : IsMatching C2) (hS : IsMatching S)
    (hs1 : ∀ e ∈ C1, e ∈ CopyEdges W E wA)
    (hs2 : ∀ e ∈ C2, e ∈ CopyEdges W E wA)
    (hsub : ∀ e ∈ S, parent e ∈ P)
    (hd1 : Disjoint (C1.image Prod.fst) (S.image Prod.fst))
    (hd2 : Disjoint (C2.image Prod.snd) (S.image Prod.snd))
    (hidx : ∀ e ∈ S, e.1.2.val + e.2.2.val + 1 = wP (parent e))
    (hmix : ∀ e ∈ P, wP e ≤ p1L e.1 + p2R e.2 + d e) :
    (C1.card : ℝ) + C2.card + S.card ≤
      ((∑ u, (p1L u : ℝ)) + ∑ v, (p1R v : ℝ)) +
      ((∑ u, (p2L u : ℝ)) + ∑ v, (p2R v : ℝ)) +
      (∑ e ∈ P, (min (rootFiber S e).card (d e) : ℝ)) := by
  have hl := deletion_left_bound (bottom_covers W E wA p1L p1R h1) hc1 hS hs1 hd1
  have hr := deletion_right_bound (bottom_covers W E wA p2L p2R h2) hc2 hS hs2 hd2
  have hc₁ := bottom_cost_le W p1L p1R
  have hc₂ := bottom_cost_le W p2L p2R
  have hm := missed_card_le_clipped W S P wP p1L p2R d hsub hidx hmix
  have hmr : ((missed S p1L p2R).card : ℝ) ≤
      ∑ e ∈ P, (min (rootFiber S e).card (d e) : ℝ) := by exact_mod_cast hm
  have hpoint (e : (L × Fin W) × (R × Fin W)) (_he : e ∈ S) :
      (1 : ℝ) ≤ (bottom W p1L p1R).left e.1 +
        (bottom W p2L p2R).right e.2 +
        (if p1L e.1.1 ≤ e.1.2.val ∧ p2R e.2.1 ≤ e.2.2.val then 1 else 0) := by
    simp only [bottom]
    split_ifs <;> norm_num at *
    omega
  have hsum := Finset.sum_le_sum hpoint
  have hmiss : (∑ e ∈ S, if p1L e.1.1 ≤ e.1.2.val ∧ p2R e.2.1 ≤ e.2.2.val
      then (1 : ℝ) else 0) = (missed S p1L p2R).card := by simp [missed]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hmiss] at hsum
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hl hr hsum
  linarith

theorem copies_of_hereditary_bound
    (W : ℕ) (E P : Finset (L × R)) (wA wP delta : L × R → ℕ) (B : ℕ)
    (hbound : ∀ M1 M2 T : Finset (L × R), IsMatching M1 → IsMatching M2 → IsMatching T →
      M1 ⊆ E → M2 ⊆ E → T ⊆ P →
      Disjoint (M1.image Prod.fst) (T.image Prod.fst) →
      Disjoint (M2.image Prod.snd) (T.image Prod.snd) →
      (∑ e ∈ M1, wA e) + (∑ e ∈ M2, wA e) + (∑ e ∈ T, (wP e-delta e)) ≤ B)
    (C1 C2 S : Finset ((L × Fin W) × (R × Fin W)))
    (hc1 : IsMatching C1) (hc2 : IsMatching C2) (hS : IsMatching S)
    (hs1 : ∀ e ∈ C1, e ∈ CopyEdges W (E : Set _) wA)
    (hs2 : ∀ e ∈ C2, e ∈ CopyEdges W (E : Set _) wA)
    (hsub : ∀ e ∈ S, parent e ∈ P)
    (hd1 : Disjoint (C1.image Prod.fst) (S.image Prod.fst))
    (hd2 : Disjoint (C2.image Prod.snd) (S.image Prod.snd))
    (hidx : ∀ e ∈ S, e.1.2.val+e.2.2.val+1=wP (parent e)) :
    C1.card+C2.card+S.card ≤ B+∑ e ∈ P, min (rootFiber S e).card (delta e) := by
  obtain ⟨p1,p2,q1,q2,h1,h2,hmix,hcost⟩ :=
    two_layer_prices_of_deletion_bound E P wA (fun e => wP e-delta e) B hbound
  have hmix' : ∀ e ∈ P, wP e ≤ p1 e.1+q2 e.2+delta e := by
    intro e he
    have hh := hmix e he
    omega
  have hh := clipped_charge_of_copy_matching W (E : Set _) P wA wP delta p1 p2 q1 q2
    h1 h2 C1 C2 S hc1 hc2 hS hs1 hs2 hsub hd1 hd2 hidx hmix'
  have hb : ((∑ l, (p1 l : ℝ))+(∑ r, (q1 r : ℝ)))+
      ((∑ l, (p2 l : ℝ))+(∑ r, (q2 r : ℝ))) ≤ (B : ℝ) := by
    have hnat : (∑ l,p1 l)+(∑ r,q1 r)+((∑ l,p2 l)+(∑ r,q2 r)) ≤ B := by omega
    exact_mod_cast hnat
  have hr : (C1.card : ℝ)+C2.card+S.card ≤
      (B : ℝ)+∑ e ∈ P, (min (rootFiber S e).card (delta e) : ℝ) := by linarith
  exact_mod_cast hr

end AbstractBipartite

section ActualHistory
open RandomOrderMatching.Graph RandomOrderMatching.Graph.WeightedMatching
open RandomOrderMatching.HistoricalDeletion.CutEncoding
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Full actual graph→historical matching→integral dual→arbitrary-copy
composition. There is no structural, price-existence, or matching bound
hypothesis. The proposal graph P can have overlapping original endpoints. -/
theorem historical_copied_matching_bound
    (cut : Finset V) (W : ℕ) (w : Edge V → ℕ) (K : ℕ → Graph V)
    (hK : ∀ i j, i ≤ j → K i ⊆ K j) (n : ℕ)
    (E P : Finset (Left cut × Right cut)) (hE : encode cut E ⊆ K 0)
    (hclosed : ∀ e ∈ encode cut P, ∃ t ≤ n,
      opt (fun f => (w f : ℝ)) (insert e (K t)) = opt (fun f => (w f : ℝ)) (K t))
    (C1 C2 S : Finset ((Left cut × Fin W) × (Right cut × Fin W)))
    (hc1 : IsMatching C1) (hc2 : IsMatching C2) (hS : IsMatching S)
    (hs1 : ∀ e ∈ C1, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p)))
    (hs2 : ∀ e ∈ C2, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p)))
    (hsub : ∀ e ∈ S, parent e ∈ P)
    (hd1 : Disjoint (C1.image Prod.fst) (S.image Prod.fst))
    (hd2 : Disjoint (C2.image Prod.snd) (S.image Prod.snd))
    (hidx : ∀ e ∈ S, e.1.2.val+e.2.2.val+1=w (edgeOf cut (parent e))) :
    C1.card+C2.card+S.card ≤ 2 * RandomOrderMatching.Phases.WeightedState.natOpt w (K n) := by
  have hb : ∀ M1 M2 T : Finset (Left cut × Right cut),
      IsMatching M1 → IsMatching M2 → IsMatching T →
      M1 ⊆ E → M2 ⊆ E → T ⊆ P →
      Disjoint (M1.image Prod.fst) (T.image Prod.fst) →
      Disjoint (M2.image Prod.snd) (T.image Prod.snd) →
      (∑ e ∈ M1,w (edgeOf cut e))+(∑ e ∈ M2,w (edgeOf cut e))+
      (∑ e ∈ T,w (edgeOf cut e)-0) ≤ 2 * RandomOrderMatching.Phases.WeightedState.natOpt w (K n) := by
    intro M1 M2 T h1 h2 ht hs1 hs2 hst hd1 hd2
    simpa using historical_triple_bound cut w K hK n E P hE hclosed M1 M2 T
      h1 h2 ht hs1 hs2 hst hd1 hd2
  have hh := copies_of_hereditary_bound W E P
    (fun p => w (edgeOf cut p)) (fun p => w (edgeOf cut p)) (fun _ => 0)
    (2 * RandomOrderMatching.Phases.WeightedState.natOpt w (K n)) hb C1 C2 S hc1 hc2 hS
    hs1 hs2 hsub hd1 hd2 hidx
  simpa using hh

end ActualHistory
end RandomOrderMatching.HistoricalDeletion.CopiedTransfer

#print axioms RandomOrderMatching.HistoricalDeletion.CopiedTransfer.historical_copied_matching_bound
