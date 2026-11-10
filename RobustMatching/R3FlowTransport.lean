import RobustMatching.R2ExactGateGraph

/-! Actual shared raw-degree transport. Root and partner edges compete for the
same center degree capacity, including the degree consumed inside the cover. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R3Flow
open R1Gate R2ExactGate

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]
  {adj : V → C → Prop} [DecidableRel adj]
  {β : ℝ} {a : V → ℝ} {dc : C → ℝ}

def rawCharge (adj : V → C → Prop) [DecidableRel adj]
    (β : ℝ) (q : V → ℝ) (s : V) (c : C) : ℝ :=
  if adj s c then q s / β else 0

lemma rawCharge_row (h : SupportData adj β a dc) (q : V → ℝ) (s : V) :
    (∑ c : C, rawCharge adj β q s c) = a s * q s := by
  unfold rawCharge
  rw [indicator_sum, h.row_degree]
  field_simp [ne_of_gt h.beta_pos]

/-- Weighted double counting on actual incidence data. -/
theorem raw_transport (h : SupportData adj β a dc)
    (X : Finset V) (q : V → ℝ) (P : C → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hP : ∀ c, 0 ≤ P c)
    (hedge : ∀ s c, adj s c → q s ≤ P c) :
    (∑ s ∈ X, a s * q s) ≤ ∑ c : C, (dc c / β) * P c := by
  have hc : ∀ c, (∑ s ∈ X, rawCharge adj β q s c) ≤ (dc c / β) * P c := by
    intro c
    calc
      (∑ s ∈ X, rawCharge adj β q s c) ≤ ∑ s : V, rawCharge adj β q s c := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X)
        intro s _ _
        unfold rawCharge
        split_ifs
        · exact div_nonneg (hq s) h.beta_pos.le
        · rfl
      _ ≤ ∑ s : V, if adj s c then P c / β else 0 := by
        apply Finset.sum_le_sum
        intro s _
        unfold rawCharge
        split_ifs with hs
        · exact div_le_div_of_nonneg_right (hedge s c hs) h.beta_pos.le
        · rfl
      _ = ((Finset.univ.filter fun s => adj s c).card : ℝ) * (P c / β) := by
        rw [indicator_sum]
      _ ≤ dc c * (P c / β) :=
        mul_le_mul_of_nonneg_right (h.column_degree c) (div_nonneg (hP c) h.beta_pos.le)
      _ = (dc c / β) * P c := by ring
  calc
    (∑ s ∈ X, a s * q s) = ∑ s ∈ X, ∑ c : C, rawCharge adj β q s c := by
      apply Finset.sum_congr rfl
      intro s _
      exact (rawCharge_row h q s).symm
    _ = ∑ c : C, ∑ s ∈ X, rawCharge adj β q s c := by rw [Finset.sum_comm]
    _ ≤ _ := Finset.sum_le_sum fun c _ => hc c

/-- Missing partners and roots share one transport budget. The hypotheses are
pointwise price inequalities; no aggregate gate or transport bound is assumed. -/
theorem shared_price_budget (h : SupportData adj β a dc)
    (S : Finset V) (M : Finset C) (partner : C → V)
    (hinj : Set.InjOn partner (M : Set C))
    (hdisj : Disjoint S (M.image partner))
    (q : V → ℝ) (P W : C → ℝ) {u k eta : ℝ}
    (hq : ∀ v, 0 ≤ q v) (hP : ∀ c, 0 ≤ P c) (hW : ∀ c, 0 ≤ W c)
    (hedge : ∀ s c, adj s c → q s ≤ P c)
    (hcenter : ∀ c, (dc c / β) * P c + W c ≤ k)
    (hpartner : ∀ c ∈ M, u ≤ a (partner c) * q (partner c) + W c + eta) :
    (∑ s ∈ S, a s * q s) + u * (M.card : ℝ) ≤
      k * Fintype.card C + eta * (M.card : ℝ) := by
  have ht := raw_transport h (S ∪ M.image partner) q P hq hP hedge
  rw [Finset.sum_union hdisj, Finset.sum_image hinj] at ht
  have hp := Finset.sum_le_sum hpartner
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hp
  have hw : (∑ c ∈ M, W c) ≤ ∑ c : C, W c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M) (fun c _ _ => hW c)
  have hb := Finset.sum_le_sum fun c (_ : c ∈ (Finset.univ : Finset C)) => hcenter c
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hb
  linarith

lemma center_price_budget {c P alpha K : ℝ}
    (hraw : c*P ≤ K-2*(1-alpha))
    (hcross : (2*c-1)*P ≤ K-2) :
    c*P + max 0 (2*alpha-(1-c)*P) ≤ K-2*(1-alpha) := by
  rw [add_max]
  apply max_le
  · simpa using hraw
  · nlinarith

lemma finite_partner_payment (R : ℝ → ℝ) {a c lam L : ℝ}
    (hmon : MonotoneOn R (Set.Icc 0 1))
    (hlip : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      R y - R x ≤ L * |y-x|)
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hc : c ∈ Set.Icc (0:ℝ) 1)
    (hL : 0 ≤ L) (hlam : 0 ≤ lam) (hsum : 1-lam ≤ a+c) :
    R (1-c) - L*lam ≤ R a := by
  have hb : 1-c ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hc.1, hc.2]
  by_cases hab : 1-c ≤ a
  · have hh := hmon hb ha hab
    nlinarith [mul_nonneg hL hlam]
  · have hh := hlip a ha (1-c) hb
    rw [abs_of_nonneg (by linarith : 0 ≤ 1-c-a)] at hh
    have hm := mul_le_mul_of_nonneg_left (show 1-c-a ≤ lam by linarith) hL
    linarith

variable {Wv : Type*} [Fintype Wv] [DecidableEq Wv]

/-- Actual graph specialization: partner separation and all raw degree
capacities follow from the graph and matching. -/
theorem shared_price_budget_of_graph
    (H G : SimpleGraph Wv) [DecidableRel H.Adj]
    (opt : G.Subgraph) (hopt : opt.IsMatching)
    (Cset : Set Wv) [DecidablePred (· ∈ Cset)] (hC : H.IsVertexCover Cset)
    {β : ℝ} (hβ : 0 < β)
    (hupper : ∀ u v, H.Adj u v → (H.degree u : ℝ)+H.degree v ≤ β)
    (S : Finset {v : Wv // v ∉ Cset}) (M : Finset {v : Wv // v ∈ Cset})
    (partner : {v : Wv // v ∈ Cset} → {v : Wv // v ∉ Cset})
    (hroot : ∀ s ∈ S, ∃ t : {v : Wv // v ∉ Cset}, opt.Adj s.val t.val)
    (hedges : ∀ c ∈ M, opt.Adj c.val (partner c).val)
    (q : {v : Wv // v ∉ Cset} → ℝ)
    (P W : {v : Wv // v ∈ Cset} → ℝ) {u k eta : ℝ}
    (hq : ∀ v, 0 ≤ q v) (hP : ∀ c, 0 ≤ P c) (hW : ∀ c, 0 ≤ W c)
    (hedge : ∀ s c, H.Adj s.val c.val → q s ≤ P c)
    (hcenter : ∀ c, ((H.degree c.val : ℝ)/β)*P c+W c ≤ k)
    (hpartner : ∀ c ∈ M, u ≤ ((H.degree (partner c).val : ℝ)/β)*q (partner c)+W c+eta) :
    (∑ s ∈ S, ((H.degree s.val : ℝ)/β)*q s) + u*(M.card : ℝ) ≤
      k * Fintype.card {v : Wv // v ∈ Cset} + eta*(M.card : ℝ) := by
  have hs := supportData_of_graph_cover H Cset hC hβ hupper
  obtain ⟨hi, hd⟩ := matching_partners_separate G opt hopt Cset S M partner hroot hedges
  exact shared_price_budget hs S M partner hi hd q P W hq hP hW hedge hcenter hpartner

end RobustMatching.R3Flow
#print axioms RobustMatching.R3Flow.raw_transport
#print axioms RobustMatching.R3Flow.shared_price_budget
#print axioms RobustMatching.R3Flow.shared_price_budget_of_graph
#print axioms RobustMatching.R3Flow.finite_partner_payment
