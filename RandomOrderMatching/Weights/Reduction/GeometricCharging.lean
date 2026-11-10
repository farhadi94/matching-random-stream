import RandomOrderMatching.Weights.Reduction.Greedy

/-! Weighted approximation bound for the actual ordered greedy union.
The finite geometric budget below is instantiated by separated weight bands. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Weights.Reduction.GeometricCharging
open RandomOrderMatching.Graph RandomOrderMatching.Weights.Reduction.Greedy
variable {V : Type*} [DecidableEq V]

theorem rejected_charge_bound (levels : ℕ → Graph V) (n : ℕ)
    (index : Edge V → ℕ) (hindex : ∀ i < n, ∀ e ∈ levels i, index e = i)
    (hM : ∀ i, Matching (levels i)) (w : Edge V → ℝ) (upper : ℕ → ℝ)
    (hupper : ∀ i < n, ∀ e ∈ levels i, w e ≤ upper i)
    (hupper0 : ∀ i, 0 ≤ upper i) {C : ℝ}
    (hbudget : ∀ f ∈ combine levels n,
      2*(∑ i ∈ (Finset.range n).filter (fun i => index f < i), upper i) ≤ C*w f) :
    (∑ e ∈ ((Finset.range n).biUnion levels) \ combine levels n, w e) ≤
      C * ∑ f ∈ combine levels n, w f := by
  classical
  let H := (Finset.range n).biUnion levels
  let M := combine levels n
  let R := H \ M
  have hblock (e : Edge V) (he : e ∈ R) :
      ∃ f ∈ M, index f < index e ∧ ¬ Disjoint e.val f.val := by
    obtain ⟨heH,heM⟩ := Finset.mem_sdiff.mp he
    obtain ⟨i,hin,hei⟩ := Finset.mem_biUnion.mp heH
    have hi := Finset.mem_range.mp hin
    obtain ⟨f,hf,j,hj,hfj,hmeet⟩ := rejected_blocker levels hi hei heM
    refine ⟨f,hf,?_,hmeet⟩
    rw [hindex i hi e hei, hindex j (by omega) f hfj]
    exact hj
  let charge : Edge V → Edge V := fun e => if he : e ∈ R then (hblock e he).choose else e
  have hcharge (e : Edge V) (he : e ∈ R) :
      charge e ∈ M ∧ index (charge e) < index e ∧ ¬ Disjoint e.val (charge e).val := by
    simp only [charge, dif_pos he]
    exact (hblock e he).choose_spec
  have hmap : ∀ e ∈ R, charge e ∈ M := fun e he => (hcharge e he).1
  have hfiber (f : Edge V) (hf : f ∈ M) :
      (∑ e ∈ R.filter (fun e => charge e = f), w e) ≤ C*w f := by
    let F := R.filter (fun e => charge e = f)
    have hlevels : ∀ e ∈ F, index e ∈ Finset.range n := by
      intro e he
      have heR := (Finset.mem_filter.mp he).1
      have heH := (Finset.mem_sdiff.mp heR).1
      obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp heH
      rw [hindex i (Finset.mem_range.mp hi) e hei]
      exact hi
    have hpart : (∑ e ∈ F, w e) =
        ∑ i ∈ Finset.range n, ∑ e ∈ F.filter (fun e => index e = i), w e :=
      (Finset.sum_fiberwise_of_maps_to hlevels w).symm
    change (∑ e ∈ F, w e) ≤ _
    rw [hpart]
    calc
      _ ≤ ∑ i ∈ Finset.range n, if index f < i then 2*upper i else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hfi : index f < i
        · rw [if_pos hfi]
          apply charge_weight (levels i) (F.filter (fun e => index e = i)) (hM i) ?_ f ?_ w
            (hupper0 i) ?_
          · intro e he
            obtain ⟨heF,hei⟩ := Finset.mem_filter.mp he
            have heH := (Finset.mem_sdiff.mp (Finset.mem_filter.mp heF).1).1
            obtain ⟨j,hj,hej⟩ := Finset.mem_biUnion.mp heH
            have hji : j = i := (hindex j (Finset.mem_range.mp hj) e hej).symm.trans hei
            simpa [hji] using hej
          · intro e he
            have heF := (Finset.mem_filter.mp he).1
            obtain ⟨heR,hecharge⟩ := Finset.mem_filter.mp heF
            simpa only [hecharge] using (hcharge e heR).2.2
          · intro e he
            obtain ⟨heF,hei⟩ := Finset.mem_filter.mp he
            have heH := (Finset.mem_sdiff.mp (Finset.mem_filter.mp heF).1).1
            obtain ⟨j,hj,hej⟩ := Finset.mem_biUnion.mp heH
            have hji : j = i := (hindex j (Finset.mem_range.mp hj) e hej).symm.trans hei
            exact hji ▸ hupper j (Finset.mem_range.mp hj) e hej
        · rw [if_neg hfi]
          have hempty : F.filter (fun e => index e = i) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro e he
            obtain ⟨heF,hei⟩ := Finset.mem_filter.mp he
            obtain ⟨heR,hecharge⟩ := Finset.mem_filter.mp heF
            have hh := (hcharge e heR).2.1
            rw [hecharge,hei] at hh
            exact hfi hh
          rw [hempty,Finset.sum_empty]
      _ = 2*(∑ i ∈ (Finset.range n).filter (fun i => index f < i), upper i) := by
        rw [← Finset.sum_filter, Finset.mul_sum]
      _ ≤ C*w f := hbudget f hf
  change (∑ e ∈ R, w e) ≤ _
  calc
    _ = ∑ f ∈ M, ∑ e ∈ R.filter (fun e => charge e = f), w e :=
      (Finset.sum_fiberwise_of_maps_to hmap w).symm
    _ ≤ ∑ f ∈ M, C*w f := Finset.sum_le_sum hfiber
    _ = C*(∑ f ∈ M, w f) := (Finset.mul_sum ..).symm

/-- Full structural guarantee: the actual greedy matching preserves all but
the finite lower-level blocking charge. -/
theorem combine_weight_bound (levels : ℕ → Graph V) (n : ℕ)
    (index : Edge V → ℕ) (hindex : ∀ i < n, ∀ e ∈ levels i, index e = i)
    (hM : ∀ i, Matching (levels i)) (w : Edge V → ℝ) (upper : ℕ → ℝ)
    (hupper : ∀ i < n, ∀ e ∈ levels i, w e ≤ upper i)
    (hupper0 : ∀ i, 0 ≤ upper i) {C : ℝ}
    (hbudget : ∀ f ∈ combine levels n,
      2*(∑ i ∈ (Finset.range n).filter (fun i => index f < i), upper i) ≤ C*w f) :
    (∑ e ∈ (Finset.range n).biUnion levels, w e) ≤
      (1+C)*(∑ f ∈ combine levels n, w f) := by
  have h := rejected_charge_bound levels n index hindex hM w upper hupper hupper0 hbudget
  have hsplit := Finset.sum_sdiff (combine_subset_union levels n) (f := w)
  linarith

theorem geometric_budget {r A B : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hA : 0 ≤ A) (hB : 0 < B) (j n : ℕ) :
    2*(∑ i ∈ (Finset.range n).filter (fun i => j < i), A*r^i/(B*r)) ≤
      (2/(B*(1-r)))*(A*r^j) := by
  have hset : (Finset.range n).filter (fun i => j < i) = Finset.Ico (j+1) n := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw [hset]
  have hs := geom_sum_Ico_le_of_lt_one hr.le hr1 (m := j+1) (n := n)
  have hc : 0 ≤ A/(B*r) := div_nonneg hA (mul_pos hB hr).le
  have hsum : (∑ i ∈ Finset.Ico (j+1) n, A*r^i/(B*r)) =
      (A/(B*r))*(∑ i ∈ Finset.Ico (j+1) n, r^i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  have hh := mul_le_mul_of_nonneg_left hs hc
  have hne : B ≠ 0 := ne_of_gt hB
  have hrne : r ≠ 0 := ne_of_gt hr
  have h1 : 1-r ≠ 0 := by linarith
  calc
    _ ≤ 2*((A/(B*r))*(r^(j+1)/(1-r))) := by linarith
    _ = _ := by rw [pow_succ]; field_simp

/-- Separated bands: level i has lower weight A*r^i and upper weight
A*r^i/(B*r). The gap between consecutive bands is B. -/
theorem separated_combine (levels : ℕ → Graph V) (n : ℕ)
    (index : Edge V → ℕ) (hindex : ∀ i < n, ∀ e ∈ levels i, index e = i)
    (hM : ∀ i, Matching (levels i)) (w : Edge V → ℝ)
    {r A B : ℝ} (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) (hB : 0 < B)
    (hweights : ∀ i < n, ∀ e ∈ levels i, A*r^i ≤ w e ∧ w e ≤ A*r^i/(B*r)) :
    (∑ e ∈ (Finset.range n).biUnion levels, w e) ≤
      (1+2/(B*(1-r)))*(∑ f ∈ combine levels n, w f) := by
  apply combine_weight_bound levels n index hindex hM w (fun i => A*r^i/(B*r))
    (fun i hi e he => (hweights i hi e he).2)
    (fun i => div_nonneg (mul_nonneg hA (pow_nonneg hr.le i)) (mul_pos hB hr).le)
  intro f hf
  obtain ⟨j,hj,hfj⟩ := combine_origin levels hf
  have hif := hindex j hj f hfj
  rw [hif]
  apply (geometric_budget hr hr1 hA hB j n).trans
  exact mul_le_mul_of_nonneg_left (hweights j hj f hfj).1
    (div_nonneg (by norm_num) (mul_pos hB (by linarith)).le)

end RandomOrderMatching.Weights.Reduction.GeometricCharging

#print axioms RandomOrderMatching.Weights.Reduction.GeometricCharging.separated_combine
