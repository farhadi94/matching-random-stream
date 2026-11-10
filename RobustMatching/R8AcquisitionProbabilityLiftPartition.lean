import RobustMatching.R8AcquisitionProbabilityStopping

/-! Integration over the actual observed stopping histories. The finite key
records the stopping time and exactly its observed labels. -/
noncomputable section
open Classical
open scoped BigOperators
namespace RobustMatching.R8AcquisitionProbability
open RobustMatching.R7ProbabilityStopping RobustMatching.R7ProbabilityPermutation

def stoppedHistoryKey {n : ℕ} (τ : Equiv.Perm (Fin n) → ℕ)
    (hbound : ∀π,τ π≤n) (π : Equiv.Perm (Fin n)) :
    Fin (n+1) × (Fin n → Option (Fin n)) :=
  (⟨τ π,by have := hbound π; omega⟩,fun i => if i.val<τ π then some (π i) else none)

theorem stoppedHistoryKey_eq_iff {n : ℕ} (τ : Equiv.Perm (Fin n) → ℕ)
    (hbound : ∀π,τ π≤n) (σ π : Equiv.Perm (Fin n)) :
    stoppedHistoryKey τ hbound π=stoppedHistoryKey τ hbound σ ↔
      π∈stoppedCylinder τ σ := by
  constructor
  · intro he
    have ht : τ π=τ σ := congrArg (fun x => x.1.val) he
    have hm := congrArg Prod.snd he
    apply Finset.mem_filter.mpr
    refine ⟨mem_cylinder.mpr ?_,ht⟩
    intro i hi
    have hil : i.val<τ σ := by simpa [positions] using hi
    have hh := congrFun hm i
    simpa only [stoppedHistoryKey,ht,if_pos hil,Option.some.injEq] using hh
  · intro hp
    obtain ⟨hc,ht⟩ := Finset.mem_filter.mp hp
    apply Prod.ext
    · exact Fin.ext ht
    · funext i
      change (if i.val<τ π then some (π i) else none)=
        (if i.val<τ σ then some (σ i) else none)
      rw [ht]
      by_cases hi : i.val<τ σ
      · simp only [if_pos hi]
        congr 1
        exact mem_cylinder.mp hc i (by simpa [positions] using hi)
      · simp only [if_neg hi]

/-- Pointwise conditional bounds on observed stopping histories integrate
to the same unconditional bound, even when the stopping time varies. -/
theorem stopped_event_bound {n : ℕ} (τ : Equiv.Perm (Fin n) → ℕ)
    (hbound : ∀π,τ π≤n) (bad : Finset (Equiv.Perm (Fin n))) (p : ℝ)
    (hlocal : ∀σ,(((stoppedCylinder τ σ).filter (fun π => π∈bad)).card : ℝ)/
      (stoppedCylinder τ σ).card≤p) :
    (bad.card : ℝ)/Fintype.card (Equiv.Perm (Fin n))≤p := by
  let key := stoppedHistoryKey τ hbound
  have htotal : (bad.card : ℝ)≤p*Fintype.card (Equiv.Perm (Fin n)) := by
    apply integrate_fiber_bound key bad p
    intro b
    by_cases hb : ∃σ,key σ=b
    · obtain ⟨σ,hσ⟩ := hb
      have hk (π : Equiv.Perm (Fin n)) : key π=b ↔ π∈stoppedCylinder τ σ := by
        rw [←hσ]
        exact stoppedHistoryKey_eq_iff τ hbound σ π
      have hall : Finset.univ.filter (fun π => key π=b)=stoppedCylinder τ σ := by
        ext π
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,hk]
      have hbad : bad.filter (fun π => key π=b)=
          (stoppedCylinder τ σ).filter (fun π => π∈bad) := by
        ext π
        simp only [Finset.mem_filter,hk,and_comm]
      have hself : σ∈stoppedCylinder τ σ := by
        apply Finset.mem_filter.mpr
        exact ⟨mem_cylinder.mpr (fun _ _ => rfl),rfl⟩
      have hpos : (0:ℝ)<(stoppedCylinder τ σ).card :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨σ,hself⟩)
      rw [hall,hbad]
      exact (div_le_iff₀ hpos).mp (hlocal σ)
    · have hempty : ∀π,¬key π=b := by intro π hp; exact hb ⟨π,hp⟩
      simp only [hempty,Finset.filter_false,Finset.card_empty,Nat.cast_zero,mul_zero,le_refl]
  exact (div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
    (0:ℝ)<Fintype.card (Equiv.Perm (Fin n)))).mpr htotal

theorem actual_stopped_event_bound {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} (hn : 0<n) (cfg : RobustMatching.R8Acquisition.Config)
    (batch : Fin n → List (RobustMatching.R2Cut.Edge V))
    (bad : Finset (Equiv.Perm (Fin n))) (p : ℝ)
    (hlocal : ∀σ,(((stoppedCylinder (acquisitionStop hn cfg batch) σ).filter
      (fun π => π∈bad)).card : ℝ)/
      (stoppedCylinder (acquisitionStop hn cfg batch) σ).card≤p) :
    (bad.card : ℝ)/Fintype.card (Equiv.Perm (Fin n))≤p :=
  stopped_event_bound _ (acquisitionStop_le hn cfg batch) bad p hlocal

end RobustMatching.R8AcquisitionProbability
