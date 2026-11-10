import RobustMatching.R3FlowTransport

/-! Actual graph foundations for the all-outside repair. These declarations
prove capped incidence bounds and internal-payment identities. They do not
claim the stochastic repair theorem or the interval LP certificate. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators

namespace RobustMatching.R7SupportFlow
open R1Gate

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

def cappedWeight (adj : V → C → Prop) [DecidableRel adj]
    (β δ : ℝ) (a : V → ℝ) (s : V) (c : C) : ℝ :=
  if adj s c then 1 / (β * max δ (1-a s)) else 0

variable {adj : V → C → Prop} [DecidableRel adj]
  {β δ : ℝ} {a : V → ℝ} {dc : C → ℝ}

lemma cappedWeight_nonneg (hβ : 0 < β) (hδ : 0 < δ) (s : V) (c : C) :
    0 ≤ cappedWeight adj β δ a s c := by
  unfold cappedWeight
  split_ifs
  · exact (one_div_pos.mpr (mul_pos hβ (lt_of_lt_of_le hδ (le_max_left _ _)))).le
  · rfl

lemma cappedWeight_le_edge_cap (hβ : 0 < β) (hδ : 0 < δ) (s : V) (c : C) :
    cappedWeight adj β δ a s c ≤ 1/(β*δ) := by
  unfold cappedWeight
  split_ifs
  · exact one_div_le_one_div_of_le (mul_pos hβ hδ)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hβ.le)
  · exact (one_div_pos.mpr (mul_pos hβ hδ)).le

lemma cappedWeight_le_original (h : SupportData adj β a dc) (s : V) (c : C) :
    cappedWeight adj β δ a s c ≤ supportWeight adj β a s c := by
  unfold cappedWeight supportWeight
  split_ifs
  · exact one_div_le_one_div_of_le (mul_pos h.beta_pos (sub_pos.mpr (h.degree_lt_one s)))
      (mul_le_mul_of_nonneg_left (le_max_right _ _) h.beta_pos.le)
  · rfl

theorem capped_column_le_one (h : SupportData adj β a dc) (c : C) :
    (∑ s, cappedWeight adj β δ a s c) ≤ 1 := by
  exact (Finset.sum_le_sum fun s _ => cappedWeight_le_original h s c).trans
    (column_support_le_one h c)

theorem capped_row_exact (h : SupportData adj β a dc) (hδ : 0 < δ) (s : V) :
    (∑ c, cappedWeight adj β δ a s c) = a s / max δ (1-a s) := by
  unfold cappedWeight
  rw [indicator_sum, h.row_degree]
  have hm : max δ (1-a s) ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ (le_max_left _ _))
  field_simp [ne_of_gt h.beta_pos, hm]

theorem capped_total_le_centers (h : SupportData adj β a dc) (hδ : 0 < δ) :
    (∑ s, a s / max δ (1-a s)) ≤ Fintype.card C := by
  calc
    (∑ s, a s / max δ (1-a s)) = ∑ s, ∑ c, cappedWeight adj β δ a s c := by
      apply Finset.sum_congr rfl
      intro s _
      exact (capped_row_exact h hδ s).symm
    _ = ∑ c, ∑ s, cappedWeight adj β δ a s c := Finset.sum_comm
    _ ≤ ∑ _c : C, (1 : ℝ) := Finset.sum_le_sum fun c _ => capped_column_le_one h c
    _ = Fintype.card C := by simp

/-- Although unmatched outside vertices can be numerous, only at most b
outside vertices have normalized degree above one half. -/
theorem large_outside_count (h : SupportData adj β a dc) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1/2) :
    ((Finset.univ.filter fun s => (1/2 : ℝ) < a s).card : ℝ) ≤ Fintype.card C := by
  let S := Finset.univ.filter fun s => (1/2 : ℝ) < a s
  have hone : ∀ s ∈ S, 1 ≤ a s / max δ (1-a s) := by
    intro s hs
    have ha : (1/2 : ℝ) < a s := (Finset.mem_filter.mp hs).2
    have hm : 0 < max δ (1-a s) := lt_of_lt_of_le hδ (le_max_left _ _)
    apply (le_div_iff₀ hm).2
    simp only [one_mul]
    apply max_le
    · linarith
    · linarith
  calc
    (S.card : ℝ) = ∑ _s ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ s ∈ S, a s / max δ (1-a s) := Finset.sum_le_sum hone
    _ ≤ ∑ s : V, a s / max δ (1-a s) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro s _ _
      exact div_nonneg (h.degree_nonneg s) (le_trans hδ.le (le_max_left _ _))
    _ ≤ Fintype.card C := capped_total_le_centers h hδ

section ActualGraph
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Joint all-outside capacity and per-edge cap are derived from the actual
graph and cover, rather than postulated for a fractional support oracle. -/
theorem capped_support_of_graph
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (Cset : Set W) [DecidablePred (· ∈ Cset)] (hC : H.IsVertexCover Cset)
    (hβ : 0 < β) (hδ : 0 < δ)
    (hupper : ∀ u v, H.Adj u v → (H.degree u : ℝ)+H.degree v ≤ β) :
    (∀ c : {v : W // v ∈ Cset},
      (∑ s : {v : W // v ∉ Cset},
        cappedWeight (fun s c => H.Adj s.val c.val) β δ
          (fun s => (H.degree s.val : ℝ)/β) s c) ≤ 1) ∧
    (∀ (s : {v : W // v ∉ Cset}) (c : {v : W // v ∈ Cset}),
      cappedWeight (fun s c => H.Adj s.val c.val) β δ
        (fun s => (H.degree s.val : ℝ)/β) s c ≤ 1/(β*δ)) := by
  have hs := supportData_of_graph_cover H Cset hC hβ hupper
  exact ⟨fun c => capped_column_le_one hs c,
    fun s c => cappedWeight_le_edge_cap hβ hδ s c⟩

def internalPayment (H : SimpleGraph W) [DecidableRel H.Adj]
    (S : Finset W) (β : ℝ) (P : W → ℝ) : ℝ :=
  ∑ c ∈ S, ∑ d ∈ S, if H.Adj c d then (P c-P d)/β else 0

/-- Every internal payment is received once: no independent center budgets
or unproved pairing of incidences is assumed. -/
theorem internal_payment_conservation (H : SimpleGraph W) [DecidableRel H.Adj]
    (S : Finset W) (β : ℝ) (P : W → ℝ) :
    internalPayment H S β P = 0 := by
  have hswap : (∑ c ∈ S, ∑ d ∈ S, if H.Adj c d then P d/β else 0) =
      ∑ c ∈ S, ∑ d ∈ S, if H.Adj c d then P c/β else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    simp only [H.adj_comm]
  calc
    internalPayment H S β P = ∑ c ∈ S, ∑ d ∈ S,
        ((if H.Adj c d then P c/β else 0) - (if H.Adj c d then P d/β else 0)) := by
      unfold internalPayment
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp [sub_div]
    _ = (∑ c ∈ S, ∑ d ∈ S, if H.Adj c d then P c/β else 0) -
      (∑ c ∈ S, ∑ d ∈ S, if H.Adj c d then P d/β else 0) := by
      simp only [Finset.sum_sub_distrib]
    _ = 0 := by rw [hswap]; ring

theorem signed_internal_degree_nonpos (H : SimpleGraph W) [DecidableRel H.Adj]
    (S : Finset W) (a : W → ℝ) (hβ : 0 < β)
    (hupper : ∀ u v, H.Adj u v → a u+a v ≤ 1) :
    (∑ c ∈ S, ∑ d ∈ S, if H.Adj c d then (2*a c-1)/β else 0) ≤ 0 := by
  have hid : (∑ c ∈ S, ∑ d ∈ S, if H.Adj c d then (2*a c-1)/β else 0) =
      (∑ c ∈ S, ∑ d ∈ S, if H.Adj c d then (a c+a d-1)/β else 0) +
      internalPayment H S β a := by
    unfold internalPayment
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> ring
  rw [hid, internal_payment_conservation, add_zero]
  apply Finset.sum_nonpos
  intro c _
  apply Finset.sum_nonpos
  intro d _
  split_ifs with hd
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hupper c d hd)) hβ.le
  · rfl

end ActualGraph
end RobustMatching.R7SupportFlow

#print axioms RobustMatching.R7SupportFlow.capped_support_of_graph
#print axioms RobustMatching.R7SupportFlow.large_outside_count
#print axioms RobustMatching.R7SupportFlow.internal_payment_conservation
#print axioms RobustMatching.R7SupportFlow.signed_internal_degree_nonpos
