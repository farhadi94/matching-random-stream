import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators

namespace RandomOrderMatching.Analysis.Repair.Reference

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

def phi (a : ℝ) : ℝ := a / (1 - a)
def residual (a0 a : ℝ) : ℝ := (a - a0)^2 / ((1-a0)^2 * (1-a))

def supportWeight (adj : V → C → Prop) [DecidableRel adj]
    (β : ℝ) (a : V → ℝ) (s : V) (c : C) : ℝ :=
  if adj s c then 1 / (β * (1 - a s)) else 0

def centerLoad (adj : V → C → Prop) [DecidableRel adj]
    (β : ℝ) (a : V → ℝ) (S : Finset V) (c : C) : ℝ :=
  ∑ s ∈ S, supportWeight adj β a s c

/-- A degree-based incidence interface. Outside vertices have all reference
neighbors among the centers; center degrees may additionally count edges
internal to the cover. No support or capacity conclusion is a hypothesis. -/
structure SupportData (adj : V → C → Prop) [DecidableRel adj]
    (β : ℝ) (a : V → ℝ) (dc : C → ℝ) : Prop where
  beta_pos : 0 < β
  degree_nonneg : ∀ s, 0 ≤ a s
  degree_lt_one : ∀ s, a s < 1
  row_degree : ∀ s, ((Finset.univ.filter (adj s)).card : ℝ) = β * a s
  column_degree : ∀ c, ((Finset.univ.filter fun s => adj s c).card : ℝ) ≤ dc c
  edge_degree : ∀ s c, adj s c → β * a s + dc c ≤ β

variable {adj : V → C → Prop} [DecidableRel adj]
  {β : ℝ} {a : V → ℝ} {dc : C → ℝ}

lemma supportWeight_nonneg (h : SupportData adj β a dc) (s : V) (c : C) :
    0 ≤ supportWeight adj β a s c := by
  unfold supportWeight
  split_ifs
  · exact le_of_lt (one_div_pos.mpr (mul_pos h.beta_pos (sub_pos.mpr (h.degree_lt_one s))))
  · rfl

lemma indicator_sum (S : Finset V) (p : V → Prop) [DecidablePred p] (x : ℝ) :
    (∑ s ∈ S, if p s then x else 0) = ((S.filter p).card : ℝ) * x := by
  rw [← Finset.sum_filter]
  simp

/-- The complete row charge is phi of the actual normalized row degree. -/
theorem row_support_exact (h : SupportData adj β a dc) (s : V) :
    (∑ c, supportWeight adj β a s c) = phi (a s) := by
  unfold supportWeight
  rw [indicator_sum, h.row_degree]
  unfold phi
  field_simp [ne_of_gt h.beta_pos, ne_of_gt (sub_pos.mpr (h.degree_lt_one s))]

/-- All outside vertices jointly respect each center's unit capacity. -/
theorem column_support_le_one (h : SupportData adj β a dc) (c : C) :
    (∑ s, supportWeight adj β a s c) ≤ 1 := by
  have hdnonneg : 0 ≤ dc c := le_trans (Nat.cast_nonneg _) (h.column_degree c)
  by_cases hd : dc c = 0
  · have hn : (Finset.univ.filter fun s => adj s c).card = 0 := by
      have hh := h.column_degree c
      rw [hd] at hh
      exact Nat.cast_eq_zero.mp (le_antisymm hh (Nat.cast_nonneg _))
    have hno : ∀ s, ¬adj s c := by
      intro s hs
      have hm : s ∈ Finset.univ.filter fun s => adj s c :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
      have := Finset.card_pos.mpr ⟨s, hm⟩
      omega
    simp [supportWeight, hno]
  · have hdpos : 0 < dc c := lt_of_le_of_ne hdnonneg (Ne.symm hd)
    have hle : (∑ s, supportWeight adj β a s c) ≤
        ∑ s : V, if adj s c then 1 / dc c else 0 := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hadj : adj s c
      · simp only [supportWeight, hadj, ↓reduceIte]
        apply one_div_le_one_div_of_le hdpos
        have := h.edge_degree s c hadj
        nlinarith
      · simp [supportWeight, hadj]
    rw [indicator_sum] at hle
    have hh : ((Finset.univ.filter fun s => adj s c).card : ℝ) * (1 / dc c) ≤ 1 := by
      rw [mul_one_div, div_le_one hdpos]
      exact h.column_degree c
    exact hle.trans hh

theorem centerLoad_le_one (h : SupportData adj β a dc) (S : Finset V) (c : C) :
    centerLoad adj β a S c ≤ 1 := by
  unfold centerLoad
  apply le_trans _ (column_support_le_one h c)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun s hs hnot => supportWeight_nonneg h s c)

/-- Root and additional partner support use distinct incidence edges. This
proves the full phi support bound, stronger than an unweighted edge count. -/
theorem outside_partner_support (h : SupportData adj β a dc)
    (S T : Finset V) (hST : Disjoint S T) :
    (∑ t ∈ T, phi (a t)) ≤ ∑ c : C, (1 - centerLoad adj β a S c) := by
  have hc : ∀ c, centerLoad adj β a T c ≤ 1 - centerLoad adj β a S c := by
    intro c
    have hh := centerLoad_le_one h (S ∪ T) c
    unfold centerLoad at *
    rw [Finset.sum_union hST] at hh
    linarith
  calc
    (∑ t ∈ T, phi (a t)) = ∑ t ∈ T, ∑ c : C, supportWeight adj β a t c := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (row_support_exact h t).symm
    _ = ∑ c : C, centerLoad adj β a T c := by
      rw [Finset.sum_comm]
      rfl
    _ ≤ _ := Finset.sum_le_sum fun c hc' => hc c

/-- Exact support accounting before the tangent expansion. -/
theorem unused_capacity_identity (h : SupportData adj β a dc) (S : Finset V) :
    (∑ c : C, (1 - centerLoad adj β a S c)) + (∑ s ∈ S, phi (a s)) =
      Fintype.card C := by
  have hr : (∑ s ∈ S, phi (a s)) = ∑ c : C, centerLoad adj β a S c := by
    calc
      _ = ∑ s ∈ S, ∑ c : C, supportWeight adj β a s c := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (row_support_exact h s).symm
      _ = _ := by rw [Finset.sum_comm]; rfl
  rw [hr, ← Finset.sum_add_distrib]
  simp

/-- The rational tangent identity is exact for finite lambda (a0=(1-lambda)/2). -/
theorem tangent_residual_identity {a0 x : ℝ} (ha0 : a0 ≠ 1) (hx : x ≠ 1) :
    phi x = phi a0 + (x-a0)/(1-a0)^2 + residual a0 x := by
  unfold phi residual
  field_simp
  <;> ring

/-- Low root residual can be localized to a center using only its actual
incident roots. This scalar inequality is the per-edge monotonicity step. -/
theorem low_residual_per_edge {a0 x y : ℝ}
    (hy : 0 < y) (hyx : y ≤ x) (hxa0 : x < a0) :
    (a0-x)^2 / x ≤ (a0-y)^2 / y := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  apply (div_le_div_iff₀ hx hy).mpr
  have hfac : (a0-y)^2*x - (a0-x)^2*y = (x-y)*(a0^2-x*y) := by ring
  have ha0 : 0 < a0 := lt_trans hx hxa0
  have hxy : x*y ≤ a0^2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr hxy)]

/-- Only roots below the tangent point contribute to the improved gate charge. -/
def lowRate (a0 x : ℝ) : ℝ :=
  if x < a0 then (a0-x)^2 / ((1-a0)^2*x) else 0

def lowResidual (a0 x : ℝ) : ℝ := if x < a0 then residual a0 x else 0

def lowAllocation (adj : V → C → Prop) [DecidableRel adj]
    (β a0 : ℝ) (a : V → ℝ) (S : Finset V) (c : C) : ℝ :=
  ∑ s ∈ S, supportWeight adj β a s c * lowRate a0 (a s)

def gateFunction (a0 x : ℝ) : ℝ := (max (a0-x) 0)^2 / ((1-a0)^2*x)

lemma lowRate_nonneg {a0 x : ℝ} (hx : 0 ≤ x) : 0 ≤ lowRate a0 x := by
  unfold lowRate
  split_ifs
  · exact div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hx)
  · rfl

lemma lowAllocation_nonneg (h : SupportData adj β a dc)
    (a0 : ℝ) (S : Finset V) (c : C) :
    0 ≤ lowAllocation adj β a0 a S c := by
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (supportWeight_nonneg h s c) (lowRate_nonneg (h.degree_nonneg s))

lemma adjacent_degree_pos (h : SupportData adj β a dc) {s : V} {c : C}
    (hadj : adj s c) : 0 < a s := by
  have hcard : 0 < (Finset.univ.filter (adj s)).card :=
    Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩⟩
  have hc : (0 : ℝ) < ((Finset.univ.filter (adj s)).card : ℝ) := by exact_mod_cast hcard
  rw [h.row_degree] at hc
  exact (mul_pos_iff.mp hc).resolve_right (fun hn => (not_lt_of_ge (le_of_lt h.beta_pos)) hn.1) |>.2

/-- Isolated low roots retain their residual budget; their allocated charge is
zero. Thus the sum of allocated charge is an inequality, not an equality. -/
lemma phi_mul_lowRate_le {a0 x : ℝ} (ha0 : a0 < 1) (hx : 0 ≤ x) (hx1 : x < 1) :
    phi x * lowRate a0 x ≤ lowResidual a0 x := by
  unfold lowRate lowResidual
  split_ifs with hlo
  · by_cases hz : x = 0
    · subst x
      simp only [phi, zero_div, mul_zero, div_zero, mul_zero]
      exact div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (by norm_num))
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
      have heq : phi x * ((a0-x)^2 / ((1-a0)^2*x)) = residual a0 x := by
        unfold phi residual
        field_simp
        <;> ring
      exact le_of_eq heq
  · simp

theorem lowAllocation_sum_le (h : SupportData adj β a dc)
    {a0 : ℝ} (ha0 : a0 < 1) (S : Finset V) :
    (∑ c : C, lowAllocation adj β a0 a S c) ≤
      ∑ s ∈ S, lowResidual a0 (a s) := by
  unfold lowAllocation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s hs
  rw [← Finset.sum_mul, row_support_exact h]
  exact phi_mul_lowRate_le ha0 (h.degree_nonneg s) (h.degree_lt_one s)

/-- The entire low-root local charge dominates the gate function times the
center's root load, directly from its incident degrees. -/
theorem lowAllocation_center_lower (h : SupportData adj β a dc)
    {a0 x : ℝ} (ha0 : a0 < 1) (hx : 0 < x) (S : Finset V) (c : C)
    (hax : ∀ s ∈ S, adj s c → a s ≤ x) :
    centerLoad adj β a S c * gateFunction a0 x ≤ lowAllocation adj β a0 a S c := by
  by_cases hxa0 : x < a0
  · unfold centerLoad lowAllocation
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s hs
    by_cases hadj : adj s c
    · have has := adjacent_degree_pos h hadj
      have hasx := hax s hs hadj
      have hslo : a s < a0 := lt_of_le_of_lt hasx hxa0
      apply mul_le_mul_of_nonneg_left _ (supportWeight_nonneg h s c)
      have ht : 0 < (1-a0)^2 := sq_pos_of_pos (sub_pos.mpr ha0)
      have hh := low_residual_per_edge has hasx hxa0
      have hh' := (div_le_div_iff_of_pos_right ht).2 hh
      simpa only [gateFunction, lowRate, hslo, ↓reduceIte,
        max_eq_left (le_of_lt (sub_pos.mpr hxa0)), div_div, mul_comm x,
        mul_comm (a s)] using hh'
    · simp [supportWeight, hadj]
  · have hf : gateFunction a0 x = 0 := by
      unfold gateFunction
      rw [max_eq_right (by linarith)]
      simp
    rw [hf, mul_zero]
    exact lowAllocation_nonneg h a0 S c

lemma phi_monotone {x y : ℝ} (hxy : x ≤ y) (hy : y < 1) : phi x ≤ phi y := by
  have hx : x < 1 := lt_of_le_of_lt hxy hy
  unfold phi
  apply (div_le_div_iff₀ (sub_pos.mpr hx) (sub_pos.mpr hy)).mpr
  nlinarith

/-- One missing crossing matching edge is paid for by unused center capacity,
low-root residual allocation, and its actual outside partner's full support. -/
theorem missing_gate_local (h : SupportData adj β a dc)
    {a0 x lam Bg Dg : ℝ} (ha0 : a0 < 1) (hx : 0 < x)
    (hBg : 0 ≤ Bg) (hDg : 0 ≤ Dg) (S : Finset V) (c : C) (t : V)
    (hax : ∀ s ∈ S, adj s c → a s ≤ x)
    (hpartner : max (x-lam) 0 ≤ a t)
    (hadmissible : 1 ≤ Bg * gateFunction a0 x + Dg * phi (max (x-lam) 0)) :
    1 ≤ (1-centerLoad adj β a S c) + Bg*lowAllocation adj β a0 a S c + Dg*phi (a t) := by
  have hlow := lowAllocation_center_lower h ha0 hx S c hax
  have hcap := centerLoad_le_one h S c
  have hw : 0 ≤ centerLoad adj β a S c :=
    Finset.sum_nonneg fun s hs => supportWeight_nonneg h s c
  have hp := phi_monotone hpartner (h.degree_lt_one t)
  have hpnonneg : 0 ≤ phi (a t) :=
    div_nonneg (h.degree_nonneg t) (le_of_lt (sub_pos.mpr (h.degree_lt_one t)))
  have had : 1 ≤ Bg * gateFunction a0 x + Dg * phi (a t) := by
    nlinarith [mul_nonneg hDg (sub_nonneg.mpr hp)]
  have hscaled := mul_le_mul_of_nonneg_left had hw
  have hscaledlow := mul_le_mul_of_nonneg_left hlow hBg
  have hspare := mul_nonneg (sub_nonneg.mpr hcap) (mul_nonneg hDg hpnonneg)
  nlinarith

/-- The strengthened missing-crossing-gate bound, with actual distinct outside
partners. Every quantity is constructed from incidence weights and normalized
degrees. In particular the premise is the scalar admissibility inequality,
not the desired aggregate bound. -/
theorem missing_gate_count (h : SupportData adj β a dc)
    {a0 lam Bg Dg : ℝ} (ha0 : a0 < 1) (hBg : 0 ≤ Bg) (hDg : 0 ≤ Dg)
    (S : Finset V) (M : Finset C) (partner : C → V) (x : C → ℝ)
    (hinj : Set.InjOn partner (M : Set C))
    (hdisj : Disjoint S (M.image partner))
    (hx : ∀ c ∈ M, 0 < x c)
    (hax : ∀ c ∈ M, ∀ s ∈ S, adj s c → a s ≤ x c)
    (hpartner : ∀ c ∈ M, max (x c-lam) 0 ≤ a (partner c))
    (hadmissible : ∀ c ∈ M,
      1 ≤ Bg * gateFunction a0 (x c) + Dg * phi (max (x c-lam) 0)) :
    (M.card : ℝ) ≤
      (1+Dg) * (∑ c : C, (1-centerLoad adj β a S c)) +
      Bg * (∑ s ∈ S, lowResidual a0 (a s)) := by
  have hpoint : ∀ c ∈ M, (1 : ℝ) ≤
      (1-centerLoad adj β a S c) + Bg*lowAllocation adj β a0 a S c +
        Dg*phi (a (partner c)) := by
    intro c hc
    exact missing_gate_local h ha0 (hx c hc) hBg hDg S c (partner c)
      (hax c hc) (hpartner c hc) (hadmissible c hc)
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hE : (∑ c ∈ M, (1-centerLoad adj β a S c)) ≤
      ∑ c : C, (1-centerLoad adj β a S c) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
      (fun c hc hn => sub_nonneg.mpr (centerLoad_le_one h S c))
  have hQ : (∑ c ∈ M, lowAllocation adj β a0 a S c) ≤
      ∑ s ∈ S, lowResidual a0 (a s) := by
    apply le_trans _ (lowAllocation_sum_le h ha0 S)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
      (fun c hc hn => lowAllocation_nonneg h a0 S c)
  have hT : (∑ c ∈ M, phi (a (partner c))) ≤
      ∑ c : C, (1-centerLoad adj β a S c) := by
    have hh := outside_partner_support h S (M.image partner) hdisj
    rw [Finset.sum_image hinj] at hh
    exact hh
  calc
    _ ≤ _ := hsum
    _ ≤ (∑ c : C, (1-centerLoad adj β a S c)) +
        Bg * (∑ s ∈ S, lowResidual a0 (a s)) +
        Dg * (∑ c : C, (1-centerLoad adj β a S c)) :=
      add_le_add (add_le_add hE (mul_le_mul_of_nonneg_left hQ hBg))
        (mul_le_mul_of_nonneg_left hT hDg)
    _ = _ := by ring

/-- Exact tangent budget, with the linear paired-degree surplus still visible. -/
theorem support_tangent_identity (h : SupportData adj β a dc)
    {a0 : ℝ} (ha0 : a0 < 1) (S : Finset V) :
    (Fintype.card C : ℝ) - (S.card : ℝ) * phi a0 =
      (∑ c : C, (1-centerLoad adj β a S c)) +
      (∑ s ∈ S, residual a0 (a s)) +
      (∑ s ∈ S, (a s-a0)) / (1-a0)^2 := by
  have ht : (∑ s ∈ S, phi (a s)) =
      (S.card : ℝ) * phi a0 +
      (∑ s ∈ S, (a s-a0)) / (1-a0)^2 +
      (∑ s ∈ S, residual a0 (a s)) := by
    simp_rw [tangent_residual_identity (ne_of_lt ha0) (ne_of_lt (h.degree_lt_one _))]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_div, Finset.sum_const]
    simp
  have hi := unused_capacity_identity h S
  linarith

lemma residual_nonneg {a0 x : ℝ} (hx : x < 1) : 0 ≤ residual a0 x :=
  div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (le_of_lt (sub_pos.mpr hx)))

/-- Under the missed-edge degree lower bound, its high endpoint pays at least
the residual of its low endpoint. This includes a zero-degree low endpoint. -/
theorem low_residual_le_partner {a0 x y : ℝ} (ha0 : a0 < 1)
    (hx : x < a0) (hy : y < 1) (hsum : 2*a0 ≤ x+y) :
    residual a0 x ≤ residual a0 y := by
  have hx1 : x < 1 := lt_trans hx ha0
  have hxy : x ≤ y := by linarith
  have hn : (x-a0)^2 ≤ (y-a0)^2 := by nlinarith
  have ht : 0 < (1-a0)^2 := sq_pos_of_pos (sub_pos.mpr ha0)
  have hdX : 0 < (1-a0)^2*(1-x) := mul_pos ht (sub_pos.mpr hx1)
  have hdY : 0 < (1-a0)^2*(1-y) := mul_pos ht (sub_pos.mpr hy)
  have hd : (1-a0)^2*(1-y) ≤ (1-a0)^2*(1-x) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_of_lt ht)
  unfold residual
  exact (div_le_div_of_nonneg_right hn (le_of_lt hdX)).trans
    (div_le_div_of_nonneg_left (sq_nonneg _) hdY hd)

/-- The improved budget: twice the low residual is at most the complete
residual, pair by pair, at finite lambda. -/
theorem paired_low_residual {a0 x y : ℝ} (ha0 : a0 < 1)
    (hx : x < 1) (hy : y < 1) (hsum : 2*a0 ≤ x+y) :
    2*(lowResidual a0 x + lowResidual a0 y) ≤ residual a0 x + residual a0 y := by
  by_cases hxl : x < a0
  · have hyl : ¬y < a0 := by linarith
    have hh := low_residual_le_partner ha0 hxl hy hsum
    simp only [lowResidual, hxl, hyl, ↓reduceIte]
    linarith
  · by_cases hyl : y < a0
    · have hh := low_residual_le_partner ha0 hyl hx (by linarith : 2*a0 ≤ y+x)
      simp only [lowResidual, hxl, hyl, ↓reduceIte]
      linarith
    · simp only [lowResidual, hxl, hyl, ↓reduceIte]
      linarith [residual_nonneg (a0 := a0) hx, residual_nonneg (a0 := a0) hy]

end RandomOrderMatching.Analysis.Repair.Reference

#print axioms RandomOrderMatching.Analysis.Repair.Reference.outside_partner_support
#print axioms RandomOrderMatching.Analysis.Repair.Reference.unused_capacity_identity
#print axioms RandomOrderMatching.Analysis.Repair.Reference.low_residual_per_edge

#print axioms RandomOrderMatching.Analysis.Repair.Reference.missing_gate_count
#print axioms RandomOrderMatching.Analysis.Repair.Reference.support_tangent_identity

#print axioms RandomOrderMatching.Analysis.Repair.Reference.paired_low_residual
