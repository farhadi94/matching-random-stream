import RandomOrderMatching.Acquisition.Probability.PermutationExecution
import RandomOrderMatching.Acquisition.Provenance

/-! The actual remaining-label classifier is exactly the frozen copied
underfull condition: unseen originals have no previously retained copies. -/
noncomputable section
open Classical
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition
open RandomOrderMatching.Probability.Permutation RandomOrderMatching.Probability.Stopping
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem permutation_inputPrefix {n : ℕ} (hn : 0<n) (π : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k≤n) :
    inputPrefix (permutationStream hn π) k=(List.ofFn π).take k := by
  apply List.ext_getElem (by simp [inputPrefix,Nat.min_eq_left hk])
  intro i hi hj
  have hik : i<k := by simpa [inputPrefix] using hi
  have hin : i<n := hik.trans_le hk
  simp only [inputPrefix,List.getElem_map,List.getElem_range,List.getElem_take,List.getElem_ofFn]
  exact permutationStream_apply hn π i hin

theorem actual_unseen_copy_new {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (π : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k≤n) (a : Fin n) (ha : a ∈ remaining (positions k) π)
    (e : Edge V) (he : e ∈ model.copies a) :
    e ∉ actualReference hn cfg model.copies π k := by
  apply unseen_parent_new cfg model (inputPrefix (permutationStream hn π) k) ?_ he
  intro hseen
  rw [permutation_inputPrefix hn π k hk] at hseen
  have hh := List.mem_toFinset.mpr hseen
  rw [ofFn_take_toFinset] at hh
  exact mem_remaining.mp ha hh

theorem actual_underfull_iff_bad_parent {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (π : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k≤n) (a : Fin n) (ha : a ∈ remaining (positions k) π) :
    a ∈ actualBadParents hn cfg model.copies k π ↔
      ∃ e ∈ model.copies a,edgeDegree (actualReference hn cfg model.copies π k) e<cfg.lower := by
  simp only [actualBadParents,Finset.mem_filter,ha,true_and]
  constructor
  · rintro ⟨e,he,hins⟩
    exact ⟨e,he,hins.2⟩
  · rintro ⟨e,he,hdeg⟩
    exact ⟨e,he,actual_unseen_copy_new hn cfg model π k hk a ha e he,hdeg⟩

end RandomOrderMatching.Acquisition.Probability
