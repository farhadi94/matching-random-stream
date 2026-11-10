import RobustMatching.R8WeightWindowsParameters

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RobustMatching.R8WeightWindows
open RobustMatching.R2Cut RobustMatching.R7ProbabilityRestriction
variable {V : Type*} [DecidableEq V]

def IsOptimum (w : Edge V → ℚ) (l : List (Edge V)) (M : Graph V) : Prop :=
  Matching M ∧ M ⊆ l.toFinset ∧ ∀ N : Graph V,Matching N → N ⊆ l.toFinset →
    (∑ e ∈ N,(w e:ℝ)) ≤ ∑ e ∈ M,(w e:ℝ)

theorem optimum_dominates_maximum (w : Edge V → ℚ) (l : List (Edge V))
    (M : Graph V) (hM : IsOptimum w l M) :
    maximum w l ≤ ∑ e ∈ M,(w e:ℝ) := by
  have h0 := hM.2.2 ∅ (by simp [Matching]) (Finset.empty_subset _)
  apply maximum_le w l (by simpa using h0)
  intro e he
  have hsingle := hM.2.2 {e} (by simp [Matching])
    (Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr he))
  simpa using hsingle

theorem maximum_perm (w : Edge V → ℚ) {l u : List (Edge V)} (h : u.Perm l) :
    maximum w u = maximum w l := by
  apply le_antisymm
  · exact maximum_le w u (maximum_nonneg w l) (fun e he => le_maximum w l (h.mem_iff.mp he))
  · exact maximum_le w l (maximum_nonneg w u) (fun e he => le_maximum w u (h.mem_iff.mpr he))

theorem original_graph_card [Fintype V] (E : Graph V) : E.card ≤ (Fintype.card V)^2 := by
  let pair : Edge V → V×V := fun e =>
    let h := Finset.card_eq_two.mp e.property
    (h.choose,h.choose_spec.choose)
  have hp : ∀ e : Edge V,e.val = {(pair e).1,(pair e).2} := by
    intro e
    exact (Finset.card_eq_two.mp e.property).choose_spec.choose_spec.2
  have hinj : Function.Injective pair := by
    intro e f hef
    apply Subtype.ext
    rw [hp e,hp f,hef]
  have hh := Fintype.card_le_of_injective pair hinj
  exact (Finset.card_le_univ E).trans (by simpa [pow_two] using hh)

namespace Parameters
variable (p : Parameters) (a : Machine V) (w : Edge V → ℚ)

theorem allWindows_perm {l u : List (Edge V)} (h : u.Perm l) :
    p.allWindows w u = p.allWindows w l := by
  unfold allWindows
  have heq : u.toFinset = l.toFinset := by
    ext e
    simpa only [List.mem_toFinset] using h.mem_iff
  rw [heq]

/-- Full arbitrary-weight random-order guarantee from the bounded-integer
machine contract. All window, retirement, rounding and decoder operations are
the concrete definitions above. The input optimum is fixed before permutation. -/
theorem arbitrary_weight_failure [Fintype V] (hn : 0 < Fintype.card V)
    (hw : ∀ e,0 < w e) {alpha epsilon delta : ℝ}
    (ha : 0 ≤ alpha) (heps : alpha-epsilon ≤ p.ratio alpha) (hd : 0 ≤ delta)
    (hc : a.Contract p.integerRange alpha delta)
    (l : List (Edge V)) (hl : l.Nodup) (M : Graph V) (hM : IsOptimum w l M) :
    permMean l (fun u => if (alpha-epsilon)*(∑ e ∈ M,(w e:ℝ)) ≤
      ∑ e ∈ p.answer a w (Fintype.card V) u,(w e:ℝ) then 0 else 1) ≤
      (p.k*(Fintype.card V)^2:ℕ)*delta := by
  have hsum : 0 ≤ ∑ e ∈ M,(w e:ℝ) := Finset.sum_nonneg
    (fun e _ => by exact_mod_cast (hw e).le)
  calc
    _ ≤ permMean l (fun u => if (∀ t ∈ p.allWindows w l,p.localGood a w alpha t u)
      then 0 else 1) := by
      apply permMean_mono
      intro u hu
      have hperm := List.mem_permutations'.mp hu
      by_cases hg : ∀ t ∈ p.allWindows w l,p.localGood a w alpha t u
      · have hsub : M ⊆ u.toFinset := by
          intro e he
          exact List.mem_toFinset.mpr (hperm.mem_iff.mpr (List.mem_toFinset.mp (hM.2.1 he)))
        have hm : maximum w u ≤ ∑ e ∈ M,(w e:ℝ) := by
          rw [maximum_perm w hperm]
          exact optimum_dominates_maximum w l M hM
        have hlocal : ∀ t ∈ p.allWindows w u,p.localGood a w alpha t u := by
          rw [p.allWindows_perm w hperm]
          exact hg
        have hout := p.answer_ratio a w hn hw ha hc.valid u M hM.1 hsub hm hlocal
        have hx := (mul_le_mul_of_nonneg_right heps hsum).trans hout
        simp only [if_pos hx]
        split_ifs <;> norm_num
      · simp only [if_neg hg]
        split_ifs <;> norm_num
    _ ≤ (p.allWindows w l).card*delta := p.all_windows_failure a w alpha delta hc l hl
    _ ≤ (p.k*(Fintype.card V)^2:ℕ)*delta := by
      apply mul_le_mul_of_nonneg_right _ hd
      exact_mod_cast (p.allWindows_count w l hw).trans
        (Nat.mul_le_mul_left p.k (original_graph_card l.toFinset))

end Parameters

/-- The advertised alpha-epsilon reduction with the actual fixed-family
failure budget delta/(k n^2). There is no dependence on the weight range. -/
theorem planned_arbitrary_weight [Fintype V] (hn : 0 < Fintype.card V)
    (a : Machine V) (w : Edge V → ℚ) (hw : ∀ e,0 < w e)
    (theta : ℚ) (ht : 0 < theta) (ht1 : theta ≤ 1)
    {alpha epsilon delta : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (htheta : (theta:ℝ) ≤ epsilon) (hd : 0 ≤ delta)
    (hc : a.Contract (planned theta ht ht1).integerRange alpha
      (delta/((planned theta ht ht1).k*(Fintype.card V)^2:ℕ)))
    (l : List (Edge V)) (hl : l.Nodup) (M : Graph V) (hM : IsOptimum w l M) :
    permMean l (fun u => if (alpha-epsilon)*(∑ e ∈ M,(w e:ℝ)) ≤
      ∑ e ∈ (planned theta ht ht1).answer a w (Fintype.card V) u,(w e:ℝ)
      then 0 else 1) ≤ delta := by
  let p := planned theta ht ht1
  have hcount : (0:ℝ) < (p.k*(Fintype.card V)^2:ℕ) := by
    exact_mod_cast Nat.mul_pos p.width_pos (pow_pos hn 2)
  have heps : alpha-epsilon ≤ p.ratio alpha :=
    (by linarith : alpha-epsilon ≤ alpha-(theta:ℝ)).trans (planned_accuracy theta ht ht1 ha ha1)
  have h := p.arbitrary_weight_failure a w hn hw ha heps
    (div_nonneg hd hcount.le) hc l hl M hM
  simpa only [mul_div_cancel₀ _ (ne_of_gt hcount)] using h

/-- A rational accuracy parameter exists for every advertised real accuracy;
choosing it above epsilon/2 also preserves the stated dependence on epsilon. -/
theorem exists_rational_accuracy {epsilon : ℝ} (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    ∃ theta : ℚ, 0 < theta ∧ theta ≤ 1 ∧ epsilon/2 < (theta:ℝ) ∧ (theta:ℝ) ≤ epsilon := by
  obtain ⟨theta,hlo,hhi⟩ := exists_rat_btwn (by linarith : epsilon/2 < epsilon)
  have ht : (0:ℝ) < (theta:ℝ) := by linarith
  have ht1 : (theta:ℝ) ≤ 1 := hhi.le.trans he1
  exact ⟨theta,by exact_mod_cast ht,by exact_mod_cast ht1,hlo,hhi.le⟩

end RobustMatching.R8WeightWindows
