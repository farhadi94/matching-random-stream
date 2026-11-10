import RandomOrderMatching.Weights.Windows.Execution

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RandomOrderMatching.Weights.Windows
open RandomOrderMatching.Graph RandomOrderMatching.Weights.Reduction.Retirement
variable {V : Type*} [DecidableEq V]

namespace Parameters
variable (p : Parameters) (a : Machine V) (w : Edge V → ℚ)

theorem localGood_transfer (hw : ∀ e,0 < w e) {alpha : ℝ} (ha : 0 ≤ alpha)
    (l : List (Edge V)) (t : ℤ) (hg : p.localGood a w alpha t l)
    (M : Graph V) (hM : Matching M) (hsub : M ⊆ l.toFinset) :
    alpha*(1-(p.eta:ℝ))*(∑ e ∈ M.filter (fun e => p.contains t (w e)),(w e:ℝ)) ≤
      ∑ e ∈ p.completeOutput a w l t,(w e:ℝ) := by
  let N := M.filter (fun e => p.contains t (w e))
  have hN : N ⊆ (p.localList w t l).toFinset := by
    intro e he
    obtain ⟨heM,het⟩ := Finset.mem_filter.mp he
    exact List.mem_toFinset.mpr (List.mem_filter.mpr
      ⟨List.mem_toFinset.mp (hsub heM),by simpa [belongs] using het⟩)
  have hi := hg N hN (matching_mono hM (Finset.filter_subset _ _))
  have hp : 0 < (p.eta:ℝ)*(p.B:ℝ)^t := mul_pos p.eta_real_pos
    (zpow_pos (lt_trans zero_lt_one p.base_real) _)
  have heq (F : Graph V) :
      (∑ e ∈ F,RandomOrderMatching.Weights.Rounding.rounded ((p.eta:ℝ)*(p.B:ℝ)^t) (w e:ℝ)) =
      ((p.eta:ℝ)*(p.B:ℝ)^t)*(∑ e ∈ F,(p.integerWeight w t e:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact (p.normalized_rounding t (w e)).symm
  apply RandomOrderMatching.Weights.Reduction.Composition.local_rounding_transfer N
    (p.completeOutput a w l t) (fun e => (w e:ℝ)) ha p.eta_real_pos
    (zpow_pos (lt_trans zero_lt_one p.base_real) _)
    (fun e => by exact_mod_cast (hw e).le)
    (fun e he => by exact_mod_cast (Finset.mem_filter.mp he).2.1)
  rw [heq,heq]
  have hh := mul_le_mul_of_nonneg_left hi hp.le
  simpa only [mul_left_comm, completeOutput] using hh

def greedyLoss : ℝ := 2/((p.B:ℝ)*(1-(p.B:ℝ)^(-((p.k+1:ℕ):ℤ))))
def ratio (alpha : ℝ) : ℝ :=
  alpha*(1-(p.eta:ℝ))*(1-(p.eta:ℝ)/2)*((p.k:ℝ)/(p.k+1))/(1+p.greedyLoss)

theorem greedyLoss_nonneg : 0 ≤ p.greedyLoss := by
  have hr : (p.B:ℝ)^(-((p.k+1:ℕ):ℤ)) < 1 := by
    rw [← zpow_zero (p.B:ℝ)]
    exact (zpow_lt_zpow_iff_right₀ p.base_real).mpr (by omega)
  unfold greedyLoss
  exact div_nonneg (by norm_num) (mul_nonneg (lt_trans zero_lt_one p.base_real).le (by linarith))

theorem ratio_nonneg {alpha : ℝ} (ha : 0 ≤ alpha) : 0 ≤ p.ratio alpha := by
  have he : (p.eta:ℝ) ≤ 1 := by exact_mod_cast p.eta_le_one
  have he0 := p.eta_real_pos
  have hc := p.greedyLoss_nonneg
  have h1 : 0 ≤ 1-(p.eta:ℝ) := by linarith
  have h2 : 0 ≤ 1-(p.eta:ℝ)/2 := by linarith
  unfold ratio
  positivity

def heavy (nVertices : ℕ) (l : List (Edge V)) (M : Graph V) : Graph V :=
  M.filter (fun e => p.finalThreshold w nVertices l ≤ (w e:ℝ))

theorem heavy_windows_live (nVertices : ℕ) (l : List (Edge V)) (M : Graph V)
    (hw : ∀ e,0 < w e) (hsub : M ⊆ l.toFinset) :
    ∀ e ∈ p.heavy w nVertices l M,p.windows (w e) ⊆ p.liveWindows w nVertices l := by
  intro e he t ht
  obtain ⟨heM,hew⟩ := Finset.mem_filter.mp he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ⟨e,hsub heM,ht⟩,?_⟩
  have hu : (w e:ℝ) < (p.B:ℝ)^(t+(p.k:ℤ)) := by
    exact_mod_cast ((p.mem_windows (hw e) t).mp ht).2
  exact hew.trans_lt hu

theorem heavy_weight [Fintype V] (hn : 0 < Fintype.card V) (l : List (Edge V))
    (M : Graph V) (hM : Matching M)
    (hmax : maximum w l ≤ ∑ e ∈ M,(w e:ℝ)) :
    (1-(p.eta:ℝ)/2)*(∑ e ∈ M,(w e:ℝ)) ≤
      ∑ e ∈ p.heavy w (Fintype.card V) l M,(w e:ℝ) := by
  have hnR : (Fintype.card V:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hth : 0 ≤ p.finalThreshold w (Fintype.card V) l :=
    mul_nonneg (div_nonneg p.eta_real_pos.le (Nat.cast_nonneg _)) (maximum_nonneg w l)
  have hh := heavy_matching_loss M hM (fun e => (w e:ℝ)) hth
  have heq : (Fintype.card V:ℝ)*p.finalThreshold w (Fintype.card V) l/2 =
      (p.eta:ℝ)*maximum w l/2 := by
    unfold finalThreshold
    field_simp
  rw [heq] at hh
  have hm := mul_le_mul_of_nonneg_left hmax p.eta_real_pos.le
  change _ ≤ ∑ e ∈ M.filter _,(w e:ℝ)
  nlinarith

/-- Pointwise actual range-reduction guarantee on the simultaneous success
event of the fixed windows. The decoder and every local benchmark are explicit. -/
theorem answer_ratio [Fintype V] (hn : 0 < Fintype.card V)
    (hw : ∀ e,0 < w e) {alpha : ℝ} (ha : 0 ≤ alpha) (hv : a.Valid)
    (l : List (Edge V)) (M : Graph V) (hM : Matching M) (hsub : M ⊆ l.toFinset)
    (hmax : maximum w l ≤ ∑ e ∈ M,(w e:ℝ))
    (hgood : ∀ t ∈ p.allWindows w l,p.localGood a w alpha t l) :
    p.ratio alpha*(∑ e ∈ M,(w e:ℝ)) ≤
      ∑ e ∈ p.answer a w (Fintype.card V) l,(w e:ℝ) := by
  let H := p.heavy w (Fintype.card V) l M
  let T := p.liveWindows w (Fintype.card V) l
  have hH : Matching H := matching_mono hM (Finset.filter_subset _ _)
  have hHsub : H ⊆ l.toFinset := (Finset.filter_subset _ _).trans hsub
  have he : (p.eta:ℝ) ≤ 1 := by exact_mod_cast p.eta_le_one
  have ha' : 0 ≤ alpha*(1-(p.eta:ℝ)) := mul_nonneg ha (by linarith)
  obtain ⟨s,hs,hgain⟩ := p.residue_approximation w hw H T (p.completeOutput a w l) ha'
    (p.heavy_windows_live w (Fintype.card V) l M hw hsub)
    (fun t _ => (p.completeOutput_valid a w hv l t).1)
    (fun t _ => (p.completeOutput_valid a w hv l t).2.2)
    (fun t ht => p.localGood_transfer a w hw ha l t
      (hgood t (Finset.mem_filter.mp ht).1) H hH hHsub)
  have hweight := p.heavy_weight w hn l M hM hmax
  have hc := p.greedyLoss_nonneg
  have hcoef : 0 ≤ alpha*(1-(p.eta:ℝ))*((p.k:ℝ)/(p.k+1))/(1+p.greedyLoss) := by
    positivity
  have hh := mul_le_mul_of_nonneg_left hweight hcoef
  have hd := p.decode_dominates w T (p.completeOutput a w l) s
  change _ ≤ ∑ e ∈ p.decode w T (p.completeOutput a w l),(w e:ℝ)
  have hg : (alpha*(1-(p.eta:ℝ))*((p.k:ℝ)/(p.k+1))/(1+p.greedyLoss))*
      (∑ e ∈ H,(w e:ℝ)) ≤ ∑ e ∈ p.decode w T (p.completeOutput a w l),(w e:ℝ) :=
    hgain.trans hd
  unfold ratio
  calc
    _ = (alpha*(1-(p.eta:ℝ))*((p.k:ℝ)/(p.k+1))/(1+p.greedyLoss))*
      ((1-(p.eta:ℝ)/2)*(∑ e ∈ M,(w e:ℝ))) := by ring
    _ ≤ _ := hh.trans hg

theorem ratio_accuracy {alpha epsilon : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hbudget : (p.eta:ℝ)+(p.eta:ℝ)/2+1/(p.k+1:ℝ)+p.greedyLoss ≤ epsilon) :
    alpha-epsilon ≤ p.ratio alpha := by
  have hz : 1/(p.k+1:ℝ) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (p.k+1:ℝ))).mpr
    have hk : (0:ℝ) ≤ p.k := Nat.cast_nonneg _
    linarith
  have h := RandomOrderMatching.Weights.Reduction.Accuracy.total_accuracy ha ha1
    p.eta_real_pos.le (div_nonneg p.eta_real_pos.le (by norm_num))
    (by positivity : 0 ≤ 1/(p.k+1:ℝ)) hz p.greedyLoss_nonneg hbudget
  have heq : 1-1/(p.k+1:ℝ) = (p.k:ℝ)/(p.k+1) := by field_simp; ring
  simpa only [heq, ratio] using h

end Parameters
end RandomOrderMatching.Weights.Windows
