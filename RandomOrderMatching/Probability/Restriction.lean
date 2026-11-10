import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RandomOrderMatching.Probability.Restriction

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem sum_map_flatMap {β : Type*} (l : List β) (g : β → List α)
    (f : α → ℝ) :
    ((l.flatMap g).map f).sum =
      (l.map (fun x => ((g x).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

/-- Removing the newly inserted label from any insertion position has the same
effect. This also permits repeated labels; the uniform-order corollary uses
distinct labels. -/
theorem filter_insertions (d : α) (l : List α) :
    ∀ u ∈ List.permutations'Aux d l,
      u.filter (fun x => x != d) = l.filter (fun x => x != d) := by
  induction l with
  | nil => simp [List.permutations'Aux]
  | cons x l ih =>
    intro u hu
    simp only [List.permutations'Aux, List.mem_cons, List.mem_map] at hu
    rcases hu with rfl | ⟨v, hv, rfl⟩
    · simp
    · simp only [List.filter_cons]
      rw [ih v hv]

theorem sum_filter_insertions (d : α) (l : List α) (f : List α → ℝ) :
    ((List.permutations'Aux d l).map
      (fun u => f (u.filter (fun x => x != d)))).sum =
      (l.length+1:ℕ)*f (l.filter (fun x => x != d)) := by
  have hmap : (List.permutations'Aux d l).map
      (fun u => f (u.filter (fun x => x != d))) =
      (List.permutations'Aux d l).map (fun _ => f (l.filter (fun x => x != d))) := by
    apply List.map_congr_left
    intro u hu
    rw [filter_insertions d l u hu]
  rw [hmap]
  simp

/-- Each real order occurs once for every possible dummy position. This is an
exact unnormalized expectation identity on all permutations of distinct labels. -/
theorem sum_delete_dummy (d : α) (l : List α) (hd : d ∉ l)
    (f : List α → ℝ) :
    (((d::l).permutations').map (fun u => f (u.filter (fun x => x != d)))).sum =
      (l.length+1:ℕ) * ((l.permutations').map f).sum := by
  rw [List.permutations', sum_map_flatMap]
  have hf (u : List α) (hu : u ∈ l.permutations') :
      u.filter (fun x => x != d) = u := by
    have hup : u.Perm l := List.mem_permutations'.mp hu
    have hdu : d ∉ u := fun h => hd (hup.mem_iff.mp h)
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [bne_iff_ne]
    intro he
    exact hdu (he ▸ hx)
  have hl (u : List α) (hu : u ∈ l.permutations') : u.length = l.length :=
    (List.mem_permutations'.mp hu).length_eq
  calc
    _ = ((l.permutations').map (fun u => (l.length+1:ℕ)*f u)).sum := by
      congr 1
      apply List.map_congr_left
      intro u hu
      rw [sum_filter_insertions, hf u hu, hl u hu]
    _ = _ := by rw [List.sum_map_mul_left]

def permMean (l : List α) (f : List α → ℝ) : ℝ :=
  ((l.permutations').map f).sum / (l.length.factorial : ℝ)

omit [DecidableEq α] in
theorem permMean_perm {l k : List α} (h : l.Perm k) (f : List α → ℝ) :
    permMean l f = permMean k f := by
  unfold permMean
  rw [h.length_eq]
  congr 1
  exact (h.permutations'.map f).sum_eq

theorem permMean_delete_dummy (d : α) (l : List α) (hd : d ∉ l)
    (f : List α → ℝ) :
    permMean (d::l) (fun u => f (u.filter (fun x => x != d))) =
      permMean l f := by
  unfold permMean
  rw [sum_delete_dummy d l hd]
  simp only [List.length_cons, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hn : (l.length : ℝ) + 1 ≠ 0 := by positivity
  have hf : (l.length.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem filter_delete_bad (p : α → Bool) (d : α) (hd : p d = false)
    (u : List α) :
    (u.filter (fun x => x != d)).filter p = u.filter p := by
  rw [List.filter_filter]
  congr 1
  funext x
  by_cases h : x = d
  · simp [h, hd]
  · simp [h]

/-- Restricting an actual uniformly permuted list of distinct labels to any
fixed subset preserves the uniform distribution on the restricted labels.
The identity applies to every real test function, not just individual labels. -/
theorem permMean_filter (l : List α) (hl : l.Nodup) (p : α → Bool)
    (f : List α → ℝ) :
    permMean l (fun u => f (u.filter p)) = permMean (l.filter p) f := by
  classical
  generalize hn : l.length = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hall : ∀ x ∈ l, p x = true
    · have hfilter : l.filter p = l := List.filter_eq_self.mpr hall
      rw [hfilter]
      unfold permMean
      congr 2
      apply List.map_congr_left
      intro u hu
      congr 1
      apply List.filter_eq_self.mpr
      intro x hx
      exact hall x ((List.mem_permutations'.mp hu).mem_iff.mp hx)
    · push Not at hall
      obtain ⟨d, hd, hpd⟩ := hall
      have hpfalse : p d = false := Bool.eq_false_iff.mpr hpd
      have hdnot : d ∉ l.filter p := by simp [List.mem_filter, hpfalse]
      have herase : (l.erase d).filter p = l.filter p := by
        rw [← List.erase_filter, List.erase_of_not_mem hdnot]
      have hshort : (l.erase d).length < n := by
        rw [List.length_erase_of_mem hd, ← hn]
        have hp : 0 < l.length := List.length_pos_of_mem hd
        omega
      calc
        permMean l (fun u => f (u.filter p)) =
            permMean (d :: l.erase d) (fun u => f (u.filter p)) :=
          permMean_perm (List.perm_cons_erase hd) _
        _ = permMean (d :: l.erase d)
            (fun u => f ((u.filter (fun x => x != d)).filter p)) := by
          congr 1
          funext u
          rw [filter_delete_bad p d hpfalse]
        _ = permMean (l.erase d) (fun u => f (u.filter p)) :=
          permMean_delete_dummy d _ hl.not_mem_erase (fun u => f (u.filter p))
        _ = permMean ((l.erase d).filter p) f :=
          ih _ hshort _ (List.Nodup.erase d hl) rfl
        _ = permMean (l.filter p) f := by rw [herase]

end RandomOrderMatching.Probability.Restriction

#print axioms RandomOrderMatching.Probability.Restriction.sum_delete_dummy
#print axioms RandomOrderMatching.Probability.Restriction.permMean_filter
