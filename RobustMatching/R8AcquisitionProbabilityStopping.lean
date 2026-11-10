import RobustMatching.R8AcquisitionProbabilityRun

/-! Causality of the particular acquisition freeze produced by its concrete
state fold, and its full residual original-label suffix law. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R8AcquisitionProbability
open RobustMatching.R8Acquisition RobustMatching.R2Cut
open RobustMatching.R7ProbabilityStopping RobustMatching.R7ProbabilityPermutation
variable {V E : Type*} [Fintype V] [DecidableEq V]

theorem actual_freeze_valid (cfg : Config) (batch : E → List (Edge V))
    (stream : ℕ → E) (k : ℕ) :
    ∀ t,(stateAt cfg batch stream k).freezeAt=some t → 0<t ∧ t≤k := by
  induction k with
  | zero => simp [stateAt,inputPrefix,run,runFrom,initialState]
  | succ k ih =>
      rw [stateAt_succ]
      have hh := step_freeze_valid cfg batch (stateAt cfg batch stream k)
        (by simpa only [stateAt_time] using ih) (stream k)
      simpa only [step_time,stateAt_time] using hh

theorem actual_freeze_persists (cfg : Config) (batch : E → List (Edge V))
    (stream : ℕ → E) (i j t : ℕ) (hij : i≤j)
    (ht : (stateAt cfg batch stream i).freezeAt=some t) :
    (stateAt cfg batch stream j).freezeAt=some t := by
  induction j with
  | zero =>
      have hi : i=0 := by omega
      simpa only [hi] using ht
  | succ j ih =>
      by_cases hi : i=j+1
      · simpa only [hi] using ht
      · have hij' : i≤j := by omega
        rw [stateAt_succ]
        exact freeze_persistent cfg batch _ _ t (ih hij')

theorem actual_freeze_restrict (cfg : Config) (batch : E → List (Edge V))
    (stream : ℕ → E) (i j t : ℕ) (hij : i ≤ j) (hti : t ≤ i)
    (ht : (stateAt cfg batch stream j).freezeAt=some t) :
    (stateAt cfg batch stream i).freezeAt=some t := by
  induction j with
  | zero =>
      have hi : i=0 := by omega
      simpa only [hi] using ht
  | succ j ih =>
      by_cases hi : i=j+1
      · simpa only [hi] using ht
      · have hij' : i≤j := by omega
        cases hs : (stateAt cfg batch stream j).freezeAt with
        | some u =>
            have hp := freeze_persistent cfg batch (stateAt cfg batch stream j) (stream j) u hs
            rw [←stateAt_succ,ht] at hp
            have he : t=u := Option.some.inj hp
            exact ih hij' (by simpa only [he] using hs)
        | none =>
            have hp := freeze_new cfg batch (stateAt cfg batch stream j) (stream j) hs
            rw [←stateAt_succ,ht,stateAt_time] at hp
            rcases hp with hp | hp
            · cases hp
            · have he := Option.some.inj hp
              omega

def acquisitionStop {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (π : Equiv.Perm (Fin n)) : ℕ :=
  (stateAt cfg batch (permutationStream hn π) n).freezeAt.getD n

theorem acquisitionStop_le {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (π : Equiv.Perm (Fin n)) :
    acquisitionStop hn cfg batch π≤n := by
  unfold acquisitionStop
  cases hs : (stateAt cfg batch (permutationStream hn π) n).freezeAt with
  | none => simp
  | some t => simpa using (actual_freeze_valid cfg batch _ n t hs).2

theorem acquisitionStop_le_iff {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k<n) :
    acquisitionStop hn cfg batch π≤k ↔
      ∃ t,(stateAt cfg batch (permutationStream hn π) k).freezeAt=some t := by
  constructor
  · intro hle
    unfold acquisitionStop at hle
    cases hs : (stateAt cfg batch (permutationStream hn π) n).freezeAt with
    | none => simp only [hs,Option.getD_none] at hle; omega
    | some t =>
        simp only [hs,Option.getD_some] at hle
        exact ⟨t,actual_freeze_restrict cfg batch _ k n t hk.le hle hs⟩
  · rintro ⟨t,ht⟩
    have hvalid := actual_freeze_valid cfg batch _ k t ht
    have hf := actual_freeze_persists cfg batch _ k n t hk.le ht
    simp only [acquisitionStop,hf,Option.getD_some]
    exact hvalid.2

theorem acquisitionStop_causal {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) : CausalStop (acquisitionStop hn cfg batch) := by
  intro k σ π hagree
  by_cases hk : k<n
  · rw [acquisitionStop_le_iff hn cfg batch σ k hk,acquisitionStop_le_iff hn cfg batch π k hk]
    have hs : stateAt cfg batch (permutationStream hn σ) k =
        stateAt cfg batch (permutationStream hn π) k := by
      apply stateAt_eq_of_prefix
      intro i hi
      have hin : i<n := hi.trans hk
      rw [permutationStream_apply _ _ _ hin,permutationStream_apply _ _ _ hin]
      exact hagree ⟨i,hin⟩ hi
    rw [hs]
  · have hn' : n≤k := Nat.le_of_not_gt hk
    exact iff_of_true ((acquisitionStop_le hn cfg batch σ).trans hn')
      ((acquisitionStop_le hn cfg batch π).trans hn')

/-- Full conditional suffix law for the ACTUAL acquisition freeze. The
stopping-rule premise is discharged by the concrete acquisition transition. -/
theorem acquisition_stopped_suffix_mean {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (σ : Equiv.Perm (Fin n))
    (f : Equiv.Perm (Fin n) → ℝ) :
    (∑ π ∈ stoppedCylinder (acquisitionStop hn cfg batch) σ,f π) /
      (stoppedCylinder (acquisitionStop hn cfg batch) σ).card =
      (∑ ν : Equiv.Perm (remaining (positions (acquisitionStop hn cfg batch σ)) σ),
        f (extendSuffix (positions (acquisitionStop hn cfg batch σ)) σ ν).val) /
          Fintype.card (Equiv.Perm (remaining (positions (acquisitionStop hn cfg batch σ)) σ)) :=
  stopped_suffix_mean _ (acquisitionStop_causal hn cfg batch) σ f

end RobustMatching.R8AcquisitionProbability
