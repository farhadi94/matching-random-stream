import RandomOrderMatching.Probability.PrefixSampling
import RandomOrderMatching.Phases.WeightedState
import RandomOrderMatching.Probability.PrefixMoments
import RandomOrderMatching.Probability.Stopping

/-! Fixed original-optimum preservation under every adaptive deletion prefix
contained in a deterministic prefix. The retained witness is an actual graph
matching, not an assumed retained-value inequality. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Probability.PrefixSampling RandomOrderMatching.Graph
open RandomOrderMatching.Phases.WeightedState RandomOrderMatching.Graph.WeightedMatching
variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

def witnessMass (label : E → Edge V) (M : Graph V) (w : Edge V → ℕ) (x : E) : ℝ :=
  if label x ∈ M then (w (label x) : ℝ) else 0

theorem witnessMass_sum (label : E → Edge V) (hi : Function.Injective label)
    (M : Graph V) (w : Edge V → ℕ) (S : Finset E) :
    (∑ x ∈ S, witnessMass label M w x) =
      ∑ e ∈ M ∩ S.image label, (w e : ℝ) := by
  have hh := Finset.sum_image (s := S) (g := label)
    (f := fun e => if e ∈ M then (w e : ℝ) else 0)
    (fun a _ b _ hab => hi hab)
  unfold witnessMass
  rw [←hh]
  rw [←Finset.sum_filter]
  congr 1
  ext e
  simp [Finset.mem_inter,and_comm]

theorem witnessMass_total (label : E → Edge V) (hi : Function.Injective label)
    (M : Graph V) (w : Edge V → ℕ) (hM : M ⊆ Finset.univ.image label) :
    (∑ x, witnessMass label M w x) = ∑ e ∈ M, (w e : ℝ) := by
  rw [witnessMass_sum label hi M w Finset.univ,Finset.inter_eq_left.mpr hM]

/-- Deleting an actual prefix loses at most its mass in the fixed witness. -/
theorem residual_witness_bound (label : E → Edge V) (hi : Function.Injective label)
    (G M : Graph V) (w : Edge V → ℕ) (hMG : M ⊆ G) (hM : Matching M)
    (A : Finset E) :
    (∑ e ∈ M, (w e : ℝ)) - (∑ x ∈ A, witnessMass label M w x) ≤
      opt (fun e => (w e : ℝ)) (G \ A.image label) := by
  have hsub : M \ A.image label ⊆ G \ A.image label := by
    intro e he
    exact Finset.mem_sdiff.mpr ⟨hMG (Finset.mem_sdiff.mp he).1,(Finset.mem_sdiff.mp he).2⟩
  have hmatch : Matching (M \ A.image label) := fun _ ha _ hb hne =>
    hM (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hne
  have hb := RandomOrderMatching.Packing.weight_le_packingOpt Matching empty_matching
    (fun e => (w e : ℝ)) hmatch hsub
  change (∑ e ∈ M \ A.image label, (w e : ℝ)) ≤ opt _ _ at hb
  rw [witnessMass_sum label hi M w A]
  have heq : (∑ e ∈ M \ A.image label, (w e : ℝ)) +
      (∑ e ∈ M ∩ A.image label, (w e : ℝ)) = ∑ e ∈ M, (w e : ℝ) := by
    have h := Finset.sum_sdiff (f := fun e => (w e : ℝ))
      (Finset.inter_subset_left : M ∩ A.image label ⊆ M)
    have he : M \ (M ∩ A.image label) = M \ A.image label := by
      ext e
      simp only [Finset.mem_sdiff,Finset.mem_inter]
      tauto
    simpa only [he] using h
  linarith

/-- Actual permutation Chernoff bound with the constant used in acquisition.
The batch coefficients may be any nonnegative values bounded by W. -/
theorem prefix_twice_mean_tail (s : Finset E) (hn : 0 < Fintype.card E)
    (r : E → ℝ) (W ρ : ℝ) (hW : 0 < W) (hρ : 0 ≤ ρ)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ W)
    (hs : (s.card : ℝ)/Fintype.card E ≤ ρ) :
    ((Finset.univ.filter (fun π : Equiv.Perm E =>
      2*ρ*(∑ x,r x) ≤ ∑ x ∈ s.image π,r x)).card : ℝ) /
      Fintype.card (Equiv.Perm E) ≤ Real.exp (-ρ*(∑ x,r x)/(3*W)) := by
  have hlog : (2/3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hμ : 0 ≤ ∑ x,r x := Finset.sum_nonneg (fun x _ => (hr x).1)
  have hscale : 0 ≤ (∑ x,r x)/W := div_nonneg hμ hW.le
  have he : Real.exp ((Real.log 2/W)*W) = 2 := by
    rw [div_mul_cancel₀ _ (ne_of_gt hW),Real.exp_log (by norm_num : (0:ℝ)<2)]
  have ht := permutation_prefix_chernoff s hn r hW
    (div_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤2)) hW.le) hr
    (B := 2*ρ*(∑ x,r x))
  rw [he] at ht
  refine ht.trans (Real.exp_le_exp.mpr ?_)
  have hs' := mul_le_mul_of_nonneg_right hs hscale
  have hl := mul_le_mul_of_nonneg_left hlog (mul_nonneg hρ hscale)
  have hid : -(Real.log 2/W)*(2*ρ*(∑ x,r x)) +
      ((s.card : ℝ)/Fintype.card E)*((∑ x,r x)/W)*(2-1) =
        -2*(ρ*((∑ x,r x)/W))*Real.log 2 +
          ((s.card : ℝ)/Fintype.card E)*((∑ x,r x)/W) := by ring
  rw [hid]
  have hrhs : -ρ*(∑ x,r x)/(3*W) = -(ρ*((∑ x,r x)/W))/3 := by ring
  rw [hrhs]
  linarith

theorem fixed_optimum_prefix_preservation
    (label : E → Edge V) (hi : Function.Injective label)
    (G : Graph V) (hG : G = Finset.univ.image label) (w : Edge V → ℕ)
    (s : Finset E) (hn : 0 < Fintype.card E) (W ρ : ℝ)
    (hW : 0 < W) (hρ : 0 ≤ ρ) (hw : ∀ e ∈ G, (w e : ℝ) ≤ W)
    (hs : (s.card : ℝ)/Fintype.card E ≤ ρ)
    (A : Equiv.Perm E → Finset E) (hA : ∀ π, A π ⊆ s.image π)
    (F : Equiv.Perm E → Graph V)
    (hF : ∀ π, G \ (A π).image label ⊆ F π) :
    ((Finset.univ.filter (fun π : Equiv.Perm E =>
      opt (fun e => (w e : ℝ)) (F π) < (1-2*ρ)*opt (fun e => (w e : ℝ)) G)).card : ℝ) /
      Fintype.card (Equiv.Perm E) ≤
        Real.exp (-ρ*opt (fun e => (w e : ℝ)) G/(3*W)) := by
  obtain ⟨M,hMG,hM,hval⟩ := natOpt_attained w G
  let r := witnessMass label M w
  have hr (x : E) : 0 ≤ r x ∧ r x ≤ W := by
    dsimp [r,witnessMass]
    split_ifs with hx
    · exact ⟨by positivity,hw _ (hMG hx)⟩
    · exact ⟨le_rfl,hW.le⟩
  have hμ : (∑ x,r x) = opt (fun e => (w e : ℝ)) G := by
    rw [witnessMass_total label hi M w (hG ▸ hMG),opt_eq_natOpt]
    exact_mod_cast hval
  have hbad : (Finset.univ.filter (fun π : Equiv.Perm E =>
      opt (fun e => (w e : ℝ)) (F π) < (1-2*ρ)*opt (fun e => (w e : ℝ)) G)) ⊆
      Finset.univ.filter (fun π : Equiv.Perm E => 2*ρ*(∑ x,r x) ≤ ∑ x ∈ s.image π,r x) := by
    intro π hπ
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hb := (Finset.mem_filter.mp hπ).2
    have hkeep := residual_witness_bound label hi G M w hMG hM (A π)
    have hmono : opt (fun e => (w e : ℝ)) (G \ (A π).image label) ≤
        opt (fun e => (w e : ℝ)) (F π) := by
      rw [opt_eq_natOpt,opt_eq_natOpt]
      exact_mod_cast natOpt_mono w (hF π)
    have hinc := RandomOrderMatching.Probability.PrefixMoments.adaptive_prefix_weight_le
      (A π) (s.image π) r (hA π) (fun x _ => (hr x).1)
    have hmval : (∑ e ∈ M,(w e : ℝ)) = opt (fun e => (w e : ℝ)) G := by
      rw [opt_eq_natOpt]
      exact_mod_cast hval
    rw [hmval] at hkeep
    rw [hμ]
    change opt _ G - (∑ x ∈ A π,r x) ≤ _ at hkeep
    linarith
  have hcard : ((Finset.univ.filter (fun π : Equiv.Perm E =>
      opt (fun e => (w e : ℝ)) (F π) < (1-2*ρ)*opt (fun e => (w e : ℝ)) G)).card : ℝ) ≤
      (Finset.univ.filter (fun π : Equiv.Perm E => 2*ρ*(∑ x,r x) ≤ ∑ x ∈ s.image π,r x)).card := by
    exact_mod_cast Finset.card_le_card hbad
  have ht := prefix_twice_mean_tail s hn r W ρ hW hρ hr hs
  rw [hμ] at ht hcard
  exact (div_le_div_of_nonneg_right hcard (by positivity)).trans ht

theorem bounded_freeze_prefix_preservation {n : ℕ}
    (label : Fin n → Edge V) (hi : Function.Injective label)
    (G : Graph V) (hG : G = Finset.univ.image label) (w : Edge V → ℕ)
    (k : ℕ) (hk : k ≤ n) (hn : 0 < n) (W ρ : ℝ)
    (hW : 0 < W) (hρ : 0 ≤ ρ) (hw : ∀ e ∈ G, (w e : ℝ) ≤ W)
    (hs : (k : ℝ)/n ≤ ρ)
    (τ : Equiv.Perm (Fin n) → ℕ) (hτ : ∀ π, τ π ≤ k)
    (F : Equiv.Perm (Fin n) → Graph V)
    (hF : ∀ π, G \ ((RandomOrderMatching.Probability.Stopping.positions (τ π)).image π).image label ⊆ F π) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      opt (fun e => (w e : ℝ)) (F π) < (1-2*ρ)*opt (fun e => (w e : ℝ)) G)).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin n)) ≤
        Real.exp (-ρ*opt (fun e => (w e : ℝ)) G/(3*W)) := by
  apply fixed_optimum_prefix_preservation label hi G hG w
    (RandomOrderMatching.Probability.Stopping.positions k) (by simpa using hn)
    W ρ hW hρ hw
    (A := fun π => (RandomOrderMatching.Probability.Stopping.positions (τ π)).image π)
    (F := F)
  · simpa only [RandomOrderMatching.Probability.Stopping.positions,Fin.card_filter_val_lt,
      Nat.min_eq_right hk,Fintype.card_fin] using hs
  · intro π
    apply Finset.image_subset_image
    intro i hi
    simp only [RandomOrderMatching.Probability.Stopping.positions,Finset.mem_filter,
      Finset.mem_univ,true_and] at hi ⊢
    exact lt_of_lt_of_le hi (hτ π)
  · exact hF

end RandomOrderMatching.Acquisition.Probability
