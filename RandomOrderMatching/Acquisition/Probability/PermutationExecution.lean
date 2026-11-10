import RandomOrderMatching.Acquisition.Probability.PrefixLists
import RandomOrderMatching.Acquisition.Invariants

/-! Sampling statements instantiated on the ACTUAL acquisition-state fold.
The remaining bad-parent classifier uses actual copied degrees and insertion
decisions. Neither a frozen reference nor its causal measurability is assumed. -/
noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition
open RandomOrderMatching.Probability.Permutation RandomOrderMatching.Probability.Stopping
variable {V : Type*} [Fintype V] [DecidableEq V]

def permutationStream {n : ℕ} (hn : 0<n) (π : Equiv.Perm (Fin n)) (i : ℕ) : Fin n :=
  if h : i<n then π ⟨i,h⟩ else π ⟨0,hn⟩

theorem permutationStream_apply {n : ℕ} (hn : 0<n) (π : Equiv.Perm (Fin n))
    (i : ℕ) (hi : i<n) : permutationStream hn π i=π ⟨i,hi⟩ := by
  simp [permutationStream,hi]

def actualReference {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (π : Equiv.Perm (Fin n)) (k : ℕ) : Graph V :=
  (stateAt cfg batch (permutationStream hn π) k).ref

theorem actualReference_prefix {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (k : ℕ) (hk : k≤n)
    (σ π : Equiv.Perm (Fin n)) (hp : π ∈ cylinder (positions k) σ) :
    actualReference hn cfg batch π k=actualReference hn cfg batch σ k := by
  unfold actualReference
  congr 1
  apply stateAt_eq_of_prefix
  intro i hi
  have hin : i<n := lt_of_lt_of_le hi hk
  rw [permutationStream_apply _ _ _ hin,permutationStream_apply _ _ _ hin]
  exact mem_cylinder.mp hp ⟨i,hin⟩ (by simpa [positions] using hi)

theorem remaining_eq_of_cylinder {n : ℕ} (k : ℕ) (σ π : Equiv.Perm (Fin n))
    (hp : π ∈ cylinder (positions k) σ) :
    remaining (positions k) π=remaining (positions k) σ := by
  unfold remaining
  congr 1
  apply Finset.image_congr
  intro i hi
  exact mem_cylinder.mp hp i hi

def actualBadParents {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (k : ℕ) (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (remaining (positions k) π).filter (fun a =>
    ∃ e ∈ batch a,insertable cfg.lower (actualReference hn cfg batch π k) e)

theorem actualBadParents_remaining {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (k : ℕ) (π : Equiv.Perm (Fin n)) :
    actualBadParents hn cfg batch k π ⊆ remaining (positions k) π :=
  Finset.filter_subset _ _

theorem actualBadParents_prefix {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (k : ℕ) (hk : k≤n)
    (σ π : Equiv.Perm (Fin n)) (hp : π ∈ cylinder (positions k) σ) :
    actualBadParents hn cfg batch k π=actualBadParents hn cfg batch k σ := by
  unfold actualBadParents
  rw [actualReference_prefix hn cfg batch k hk σ π hp,remaining_eq_of_cylinder k σ π hp]

/-- Actual acquisition references are computed from the input prefix, so the
union bound needs no assumed measurable classifier or assumed cap-success law. -/
theorem actual_bad_epoch_union_bound {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (Q Γ : ℕ) (hfit : Q*cfg.epochLength≤n) :
    ((badEpochUnion cfg.epochLength Q Γ
      (fun j => actualBadParents hn cfg batch (j*cfg.epochLength))).card : ℝ) /
        Fintype.card (Equiv.Perm (Fin n)) ≤
      Q*Real.exp (-(cfg.epochLength : ℝ)*Γ/n) := by
  apply bad_epoch_union_bound cfg.epochLength Q Γ cfg.epoch_pos hfit
  · intro j hj π
    exact actualBadParents_remaining hn cfg batch _ π
  · intro j hj σ π hp
    exact actualBadParents_prefix hn cfg batch _
      ((Nat.mul_le_mul_right cfg.epochLength (Nat.le_of_lt hj)).trans hfit) σ π hp

end RandomOrderMatching.Acquisition.Probability
