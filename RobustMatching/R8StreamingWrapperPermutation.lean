import RobustMatching.R8StreamingWrapperWitness
import RobustMatching.R7ProbabilityRestriction
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R7ProbabilityRestriction
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem labelledStream_injective {m : ℕ} (label : Fin m → Edge V)
    (hi : Function.Injective label) : Function.Injective (labelledStream label) := by
  intro pi sigma he
  have hh := (List.map_injective_iff.mpr hi) he
  apply Equiv.ext
  exact congrFun (List.ofFn_injective hh)

theorem labelledStream_perm {m : ℕ} (label : Fin m → Edge V)
    (hi : Function.Injective label) (pi : Equiv.Perm (Fin m)) :
    (labelledStream label pi).Perm (List.ofFn label) := by
  apply List.perm_of_nodup_nodup_toFinset_eq (labelledStream_nodup label hi pi)
    (List.nodup_ofFn.mpr hi)
  rw [labelledStream_toFinset]
  ext e
  simp

theorem labelledStream_all_permutations {m : ℕ} (label : Fin m → Edge V)
    (hi : Function.Injective label) :
    Finset.univ.image (labelledStream label) = (List.ofFn label).permutations'.toFinset := by
  have hnd := (List.permutations_perm_permutations' (List.ofFn label)).nodup_iff.mp
    (List.nodup_permutations _ (List.nodup_ofFn.mpr hi))
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    obtain ⟨pi,_,rfl⟩ := Finset.mem_image.mp hu
    exact List.mem_toFinset.mpr (List.mem_permutations'.mpr (labelledStream_perm label hi pi))
  · rw [Finset.card_image_of_injective _ (labelledStream_injective label hi),
      Finset.card_univ,Fintype.card_perm,Fintype.card_fin,List.toFinset_card_of_nodup hnd]
    have hh := (List.permutations_perm_permutations' (List.ofFn label)).length_eq
    rw [List.length_permutations,List.length_ofFn] at hh
    exact hh.ge

/-- Exact equality of finite permutation averages. This converts the actual
label-permutation experiment to the compiler's list-permutation interface. -/
theorem permMean_labelled {m : ℕ} (label : Fin m → Edge V)
    (hi : Function.Injective label) (f : List (Edge V) → ℝ) :
    permMean (List.ofFn label) f =
      (∑ pi : Equiv.Perm (Fin m),f (labelledStream label pi)) /
        Fintype.card (Equiv.Perm (Fin m)) := by
  have hnd := (List.permutations_perm_permutations' (List.ofFn label)).nodup_iff.mp
    (List.nodup_permutations _ (List.nodup_ofFn.mpr hi))
  unfold permMean
  rw [←List.sum_toFinset f hnd,←labelledStream_all_permutations label hi,
    Finset.sum_image (fun _ _ _ _ h => labelledStream_injective label hi h)]
  simp only [List.length_ofFn,Fintype.card_perm,Fintype.card_fin]

theorem permMean_actual_list (l : List (Edge V)) (hnd : l.Nodup)
    (f : List (Edge V) → ℝ) :
    permMean l f =
      (∑ pi : Equiv.Perm (Fin l.length),f (labelledStream l.get pi)) /
        Fintype.card (Equiv.Perm (Fin l.length)) := by
  have hh := permMean_labelled l.get hnd.injective_get f
  simpa only [List.ofFn_get] using hh

/-- Failure probability in the list-permutation contract is literally the
fraction of original-label permutations for which the operational event fails. -/
theorem permMean_failure_fraction (l : List (Edge V)) (hnd : l.Nodup)
    (Good : List (Edge V) → Prop) :
    permMean l (fun u => if Good u then 0 else 1) =
      ((Finset.univ.filter (fun pi : Equiv.Perm (Fin l.length) =>
        ¬Good (labelledStream l.get pi))).card:ℝ) /
        Fintype.card (Equiv.Perm (Fin l.length)) := by
  rw [permMean_actual_list l hnd]
  congr 1
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro pi _
  split_ifs <;> simp_all

end RobustMatching.R8StreamingWrapper
#print axioms RobustMatching.R8StreamingWrapper.permMean_actual_list
#print axioms RobustMatching.R8StreamingWrapper.permMean_failure_fraction
