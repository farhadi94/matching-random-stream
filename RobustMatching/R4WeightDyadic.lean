import RobustMatching.R4WeightTruncation

/-! Finite dyadic slope counting and increment assembly. The mesh hypotheses
are endpoint comparisons for the explicit affine pieces, not a Lipschitz bound.
Sorting the finitely many breakpoints supplies such a mesh in the paper proof. -/
open scoped BigOperators
namespace RobustMatching.R4WeightDyadic
open RobustMatching.R4WeightTruncation
noncomputable def lo (i : ℤ) : ℝ := (2:ℝ)^i
noncomputable def up (k : ℕ) (i : ℤ) : ℝ := lo (i+(k:ℤ))
lemma lo_pos (i : ℤ) : 0 < lo i := zpow_pos (by norm_num) _
lemma lo_mono {i j : ℤ} (h : i ≤ j) : lo i ≤ lo j :=
  zpow_le_zpow_right₀ (by norm_num) h
lemma lo_succ (i : ℤ) : lo (i+1) = 2*lo i := by
  simp [lo, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), mul_comm]
lemma twice_lo_le_up (k : ℕ) (hk : 1 ≤ k) (i : ℤ) : 2*lo i ≤ up k i := by
  rw [← lo_succ]
  exact lo_mono (by omega)
noncomputable def fourSet (T : Finset ℤ) (x : ℝ) : Finset ℤ :=
  T.filter (fun i => lo i/4 < x ∧ x < lo i/2)
noncomputable def oneSet (T : Finset ℤ) (k : ℕ) (x : ℝ) : Finset ℤ :=
  T.filter (fun i => lo i/2 < x ∧ x < up k i-lo i/2)

theorem four_count (T : Finset ℤ) (x : ℝ) : (fourSet T x).card ≤ 1 := by
  change (fourSet T x).card ≤ 0+1
  apply integer_diameter_card
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  by_contra h
  have hij : i+1 ≤ j := by omega
  have hp : 2*lo i ≤ lo j := by simpa [lo_succ] using lo_mono hij
  linarith

theorem one_count (T : Finset ℤ) (k : ℕ) (x : ℝ) : (oneSet T k x).card ≤ k+1 := by
  apply integer_diameter_card
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  by_contra h
  have hij : i+(k:ℤ)+1 ≤ j := by omega
  have hp : 2*up k i ≤ lo j := by
    simpa [up, lo_succ] using lo_mono hij
  have hpos := lo_pos i
  linarith

/-- All possible affine regimes on a closed interval. -/
def Piece (L U a b : ℝ) : Prop :=
  b ≤ L/4 ∨ (L/4 ≤ a ∧ b ≤ L/2) ∨
  (L/2 ≤ a ∧ b ≤ U-L/2) ∨ U-L/2 ≤ a

/-- Recover the exact slope from endpoint regime comparisons. -/
theorem piece_increment {L U a b : ℝ} (hL : 0 ≤ L) (hLU : 2*L ≤ U)
    (hab : a < b) (hp : Piece L U a b) :
    trunc L U b - trunc L U a =
      (if L/4 < (a+b)/2 ∧ (a+b)/2 < L/2 then 4*(b-a) else 0) +
      (if L/2 < (a+b)/2 ∧ (a+b)/2 < U-L/2 then b-a else 0) := by
  rcases hp with h | ⟨h1,h2⟩ | ⟨h1,h2⟩ | h
  · rw [trunc_piece_zero (by linarith) h,
        trunc_piece_zero (by linarith) (by linarith)]
    have ha : ¬ (L/4 < (a+b)/2 ∧ (a+b)/2 < L/2) := by rintro ⟨h,_⟩; linarith
    have hb : ¬ (L/2 < (a+b)/2 ∧ (a+b)/2 < U-L/2) := by rintro ⟨h,_⟩; linarith
    simp [ha,hb]
  · rw [trunc_piece_four (by linarith) (by linarith) h2,
        trunc_piece_four (by linarith) h1 (by linarith)]
    have ha : L/4 < (a+b)/2 ∧ (a+b)/2 < L/2 := by constructor <;> linarith
    have hb : ¬ (L/2 < (a+b)/2 ∧ (a+b)/2 < U-L/2) := by rintro ⟨h,_⟩; linarith
    simp [ha,hb] <;> ring
  · rw [trunc_piece_one hL (by linarith) h2,
        trunc_piece_one hL h1 (by linarith)]
    have ha : ¬ (L/4 < (a+b)/2 ∧ (a+b)/2 < L/2) := by rintro ⟨_,h⟩; linarith
    have hb : L/2 < (a+b)/2 ∧ (a+b)/2 < U-L/2 := by constructor <;> linarith
    simp [ha,hb] <;> ring
  · rw [trunc_piece_cap hL hLU (by linarith), trunc_piece_cap hL hLU h]
    have ha : ¬ (L/4 < (a+b)/2 ∧ (a+b)/2 < L/2) := by rintro ⟨_,h⟩; linarith
    have hb : ¬ (L/2 < (a+b)/2 ∧ (a+b)/2 < U-L/2) := by rintro ⟨_,h⟩; linarith
    simp [ha,hb]

/-- The k+5 bound on a single mesh cell is derived from actual dyadic labels. -/
theorem cell_increment (T : Finset ℤ) (k : ℕ) (hk : 1 ≤ k) (a b : ℝ)
    (hab : a ≤ b) (hp : ∀ i ∈ T, Piece (lo i) (up k i) a b) :
    (∑ i ∈ T, (trunc (lo i) (up k i) b-trunc (lo i) (up k i) a)) ≤
      ((k:ℝ)+5)*(b-a) := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let x := (a+b)/2
  have heq : (∑ i ∈ T, (trunc (lo i) (up k i) b-trunc (lo i) (up k i) a)) =
      ((fourSet T x).card:ℝ)*(4*(b-a)) + ((oneSet T k x).card:ℝ)*(b-a) := by
    calc
      _ = ∑ i ∈ T,
          ((if lo i/4 < x ∧ x < lo i/2 then 4*(b-a) else 0) +
          (if lo i/2 < x ∧ x < up k i-lo i/2 then b-a else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact piece_increment (lo_pos i).le (twice_lo_le_up k hk i) hab (hp i hi)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [fourSet, oneSet, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [heq]
  have h4 : ((fourSet T x).card:ℝ) ≤ 1 := by exact_mod_cast four_count T x
  have h1 : ((oneSet T k x).card:ℝ) ≤ (k:ℝ)+1 := by exact_mod_cast one_count T k x
  nlinarith

/-- Finite mesh assembly; all local costs are derived, then telescope. -/
theorem mesh_increment (T : Finset ℤ) (k m : ℕ) (hk : 1 ≤ k) (p : ℕ → ℝ)
    (hmono : ∀ j < m, p j ≤ p (j+1))
    (hpiece : ∀ j < m, ∀ i ∈ T, Piece (lo i) (up k i) (p j) (p (j+1))) :
    (∑ i ∈ T, (trunc (lo i) (up k i) (p m)-trunc (lo i) (up k i) (p 0))) ≤
      ((k:ℝ)+5)*(p m-p 0) := by
  have hc : ∑ j ∈ Finset.range m,
      (∑ i ∈ T, (trunc (lo i) (up k i) (p (j+1))-trunc (lo i) (up k i) (p j))) ≤
      ∑ j ∈ Finset.range m, ((k:ℝ)+5)*(p (j+1)-p j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact cell_increment T k hk _ _ (hmono j (Finset.mem_range.mp hj))
      (hpiece j (Finset.mem_range.mp hj))
  rw [Finset.sum_comm] at hc
  have ht (i : ℤ) : (∑ j ∈ Finset.range m,
      (trunc (lo i) (up k i) (p (j+1))-trunc (lo i) (up k i) (p j))) =
      trunc (lo i) (up k i) (p m)-trunc (lo i) (up k i) (p 0) :=
    Finset.sum_range_sub (fun j => trunc (lo i) (up k i) (p j)) m
  simp_rw [ht] at hc
  rw [← Finset.mul_sum, Finset.sum_range_sub] at hc
  exact hc
end RobustMatching.R4WeightDyadic
#print axioms RobustMatching.R4WeightDyadic.four_count
#print axioms RobustMatching.R4WeightDyadic.one_count
#print axioms RobustMatching.R4WeightDyadic.mesh_increment
