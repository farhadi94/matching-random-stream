import RandomOrderMatching.Analysis.Repair.ReferenceGraph

/-! The exact gate charge on actual finite incidence support. -/
noncomputable section
open scoped BigOperators

namespace RandomOrderMatching.Analysis.Repair.Gates
open RandomOrderMatching.Analysis.Repair.Reference

def gateFactor (lam D a : ℝ) : ℝ := max 0 (1-D*phi (max (a-lam) 0))
def exactGateProfile (lam D a : ℝ) : ℝ := phi a * gateFactor lam D a

lemma gateFactor_nonneg (lam D a : ℝ) : 0 ≤ gateFactor lam D a := le_max_left _ _

lemma exactGateProfile_nonneg {lam D a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    0 ≤ exactGateProfile lam D a :=
  mul_nonneg (div_nonneg ha (by linarith)) (gateFactor_nonneg _ _ _)

lemma gateFactor_antitone {lam D x y : ℝ} (hD : 0 ≤ D) (hxy : x ≤ y)
    (hy : max (y-lam) 0 < 1) : gateFactor lam D y ≤ gateFactor lam D x := by
  unfold gateFactor
  apply max_le_max_left
  have hp := phi_monotone (max_le_max_right 0 (by linarith : x-lam ≤ y-lam)) hy
  nlinarith [mul_nonneg hD (sub_nonneg.mpr hp)]

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]
  {adj : V → C → Prop} [DecidableRel adj]
  {β : ℝ} {a : V → ℝ} {dc : C → ℝ}

def allocation (adj : V → C → Prop) [DecidableRel adj]
    (β lam D : ℝ) (a : V → ℝ) (S : Finset V) (c : C) : ℝ :=
  ∑ s ∈ S, supportWeight adj β a s c * gateFactor lam D (a s)

lemma allocation_nonneg (h : SupportData adj β a dc) (lam D : ℝ)
    (S : Finset V) (c : C) : 0 ≤ allocation adj β lam D a S c :=
  Finset.sum_nonneg fun s _ =>
    mul_nonneg (supportWeight_nonneg h s c) (gateFactor_nonneg _ _ _)

lemma allocation_sum (h : SupportData adj β a dc) (lam D : ℝ) (S : Finset V) :
    (∑ c : C, allocation adj β lam D a S c) =
      ∑ s ∈ S, exactGateProfile lam D (a s) := by
  unfold allocation exactGateProfile
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.sum_mul, row_support_exact h]

/-- A missing center is paid using its actual distinct optimum partner.
No gate admissibility inequality is assumed. -/
theorem exact_missing_gate_local (h : SupportData adj β a dc)
    {lam D x : ℝ} (hD : 0 ≤ D) (S : Finset V) (c : C) (t : V)
    (hax : ∀ s ∈ S, adj s c → a s ≤ x)
    (hpartner : max (x-lam) 0 ≤ a t) :
    1 ≤ (1-centerLoad adj β a S c) + allocation adj β lam D a S c +
      D*phi (a t) := by
  have hx : max (x-lam) 0 < 1 := lt_of_le_of_lt hpartner (h.degree_lt_one t)
  have hp := phi_monotone hpartner (h.degree_lt_one t)
  have hpn : 0 ≤ phi (a t) := div_nonneg (h.degree_nonneg t) (by linarith [h.degree_lt_one t])
  have hw : 0 ≤ centerLoad adj β a S c :=
    Finset.sum_nonneg fun s _ => supportWeight_nonneg h s c
  have hcap := centerLoad_le_one h S c
  have hlower : centerLoad adj β a S c * gateFactor lam D x ≤
      allocation adj β lam D a S c := by
    unfold centerLoad allocation
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s hs
    by_cases hadj : adj s c
    · exact mul_le_mul_of_nonneg_left
        (gateFactor_antitone hD (hax s hs hadj) hx) (supportWeight_nonneg h s c)
    · simp [supportWeight, hadj]
  have hk : 1 ≤ gateFactor lam D x + D*phi (a t) := by
    have hm := le_max_right 0 (1-D*phi (max (x-lam) 0))
    unfold gateFactor
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hp)]
  have hscaled := mul_le_mul_of_nonneg_left hk hw
  have hspare := mul_nonneg (sub_nonneg.mpr hcap) (mul_nonneg hD hpn)
  nlinarith

/-- Exact missing-crossing count from degree incidence data, injective partners,
and root/partner disjointness. Support competition is proved by RandomOrderMatching.Analysis.Repair.Reference. -/
theorem exact_missing_gate_count (h : SupportData adj β a dc)
    {lam D : ℝ} (hD : 0 ≤ D)
    (S : Finset V) (M : Finset C) (partner : C → V) (x : C → ℝ)
    (hinj : Set.InjOn partner (M : Set C))
    (hdisj : Disjoint S (M.image partner))
    (hax : ∀ c ∈ M, ∀ s ∈ S, adj s c → a s ≤ x c)
    (hpartner : ∀ c ∈ M, max (x c-lam) 0 ≤ a (partner c)) :
    (M.card : ℝ) ≤
      (1+D)*(∑ c : C, (1-centerLoad adj β a S c)) +
      ∑ s ∈ S, exactGateProfile lam D (a s) := by
  have hsum := Finset.sum_le_sum fun c hc =>
    exact_missing_gate_local h hD S c (partner c) (hax c hc) (hpartner c hc)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hE : (∑ c ∈ M, (1-centerLoad adj β a S c)) ≤
      ∑ c : C, (1-centerLoad adj β a S c) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
      (fun c _ _ => sub_nonneg.mpr (centerLoad_le_one h S c))
  have hQ : (∑ c ∈ M, allocation adj β lam D a S c) ≤
      ∑ s ∈ S, exactGateProfile lam D (a s) := by
    rw [← allocation_sum h]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
      (fun c _ _ => allocation_nonneg h lam D S c)
  have hT : (∑ c ∈ M, phi (a (partner c))) ≤
      ∑ c : C, (1-centerLoad adj β a S c) := by
    have hh := outside_partner_support h S (M.image partner) hdisj
    rw [Finset.sum_image hinj] at hh
    exact hh
  nlinarith [mul_le_mul_of_nonneg_left hT hD]

/-- Adds the centers having no crossing optimum edge, via the independently
proved actual matching count `exceptional ≤ 2 z`. -/
theorem total_missing_gate_count (h : SupportData adj β a dc)
    {lam D d z : ℝ} (hD : 0 ≤ D)
    (S : Finset V) (M : Finset C) (partner : C → V) (x : C → ℝ)
    (hinj : Set.InjOn partner (M : Set C))
    (hdisj : Disjoint S (M.image partner))
    (hax : ∀ c ∈ M, ∀ s ∈ S, adj s c → a s ≤ x c)
    (hpartner : ∀ c ∈ M, max (x c-lam) 0 ≤ a (partner c))
    (hexceptional : d ≤ 2*z + M.card) :
    d ≤ 2*z + (1+D)*(∑ c : C, (1-centerLoad adj β a S c)) +
      ∑ s ∈ S, exactGateProfile lam D (a s) := by
  have hh := exact_missing_gate_count h hD S M partner x hinj hdisj hax hpartner
  linarith

end RandomOrderMatching.Analysis.Repair.Gates

#print axioms RandomOrderMatching.Analysis.Repair.Gates.exact_missing_gate_local
#print axioms RandomOrderMatching.Analysis.Repair.Gates.exact_missing_gate_count
#print axioms RandomOrderMatching.Analysis.Repair.Gates.total_missing_gate_count
