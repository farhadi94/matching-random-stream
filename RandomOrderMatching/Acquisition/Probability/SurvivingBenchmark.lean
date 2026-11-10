import RandomOrderMatching.Acquisition.Probability.StopBound

/-! The surviving part of a fixed original matching at the actual freeze.
The benchmark is fixed before the permutation; its surviving edge set, rather
than the optimum of a larger host, is the random variable in the tail bound. -/
noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Graph.WeightedMatching
open RandomOrderMatching.Probability.Stopping RandomOrderMatching.Probability.Permutation
variable {V O : Type*} [Fintype V] [DecidableEq V] [DecidableEq O]

def actualSurvivingWitness {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (label : Fin n → Edge O)
    (M : Graph O) (π : Equiv.Perm (Fin n)) : Graph O :=
  M \ ((positions (acquisitionStop hn cfg batch π)).image π).image label

theorem actualSurvivingWitness_spec {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (label : Fin n → Edge O)
    (M : Graph O) (hM : Matching M) (hMG : M ⊆ Finset.univ.image label)
    (π : Equiv.Perm (Fin n)) :
    Matching (actualSurvivingWitness hn cfg batch label M π) ∧
      actualSurvivingWitness hn cfg batch label M π ⊆ M ∧
      actualSurvivingWitness hn cfg batch label M π ⊆
        (((List.ofFn π).drop (acquisitionStop hn cfg batch π)).toFinset.image label) := by
  have hsub : actualSurvivingWitness hn cfg batch label M π ⊆ M := Finset.sdiff_subset
  refine ⟨fun _ ha _ hb hne => hM (hsub ha) (hsub hb) hne,hsub,?_⟩
  intro e he
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (hMG (hsub he))
  apply Finset.mem_image.mpr
  refine ⟨a,List.mem_toFinset.mpr ?_,rfl⟩
  apply (ofFn_drop_mem_remaining π _ a).mpr
  apply mem_remaining.mpr
  intro hseen
  exact (Finset.mem_sdiff.mp he).2 (Finset.mem_image_of_mem label hseen)

theorem actualSurvivingWitness_weight {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (label : Fin n → Edge O)
    (hi : Function.Injective label) (M : Graph O) (w : Edge O → ℕ)
    (π : Equiv.Perm (Fin n)) :
    (∑ e ∈ actualSurvivingWitness hn cfg batch label M π,(w e : ℝ)) =
      (∑ e ∈ M,(w e : ℝ)) -
        ∑ a ∈ (positions (acquisitionStop hn cfg batch π)).image π,witnessMass label M w a := by
  rw [witnessMass_sum label hi]
  let A := ((positions (acquisitionStop hn cfg batch π)).image π).image label
  have h := Finset.sum_sdiff (f := fun e => (w e : ℝ))
    (Finset.inter_subset_left : M ∩ A ⊆ M)
  have he : M \ (M ∩ A)=M \ A := by
    ext e
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [he] at h
  change (∑ e ∈ M \ A,(w e : ℝ))=(∑ e ∈ M,(w e : ℝ))-(∑ e ∈ M ∩ A,(w e : ℝ))
  linarith

/-- The fixed benchmark remaining after the freeze is fixed on the actual
observed stopping history, before any suffix-repair conditioning. -/
theorem actualSurvivingWitness_eq_on_stopped_history {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (label : Fin n → Edge O) (M : Graph O)
    (σ π : Equiv.Perm (Fin n))
    (hp : π ∈ stoppedCylinder (acquisitionStop hn cfg batch) σ) :
    actualSurvivingWitness hn cfg batch label M π=actualSurvivingWitness hn cfg batch label M σ := by
  rw [stoppedCylinder_eq _ (acquisitionStop_causal hn cfg batch) σ] at hp
  have hstop := stop_eq_on_cylinder _ (acquisitionStop_causal hn cfg batch) σ π hp
  have himage : (positions (acquisitionStop hn cfg batch σ)).image π=
      (positions (acquisitionStop hn cfg batch σ)).image σ :=
    Finset.image_congr (fun i hi => mem_cylinder.mp hp i hi)
  simp only [actualSurvivingWitness,hstop,himage]

/-- Exact tail for the surviving portion of any original matching fixed
before the permutation. Its matching property is exposed separately above. -/
theorem actual_fixed_witness_preserved {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (label : Fin n → Edge O) (hi : Function.Injective label)
    (M : Graph O) (hMG : M ⊆ Finset.univ.image label)
    (w : Edge O → ℕ) (W ρ : ℝ) (hW : 0<W) (hρ : 0≤ρ)
    (hw : ∀ e ∈ M,(w e : ℝ)≤W)
    (hfit : operationBound (V:=V) cfg.beta*cfg.epochLength≤n)
    (hfrac : ((operationBound (V:=V) cfg.beta*cfg.epochLength : ℕ) : ℝ)/n≤ρ) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (∑ e ∈ actualSurvivingWitness hn cfg batch label M π,(w e : ℝ)) <
        (1-2*ρ)*(∑ e ∈ M,(w e : ℝ)))).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin n)) ≤
        Real.exp (-ρ*(∑ e ∈ M,(w e : ℝ))/(3*W)) := by
  let k := operationBound (V:=V) cfg.beta*cfg.epochLength
  let r := witnessMass label M w
  have hr (a : Fin n) : 0≤r a ∧ r a≤W := by
    dsimp [r,witnessMass]
    split_ifs with ha
    · exact ⟨by positivity,hw _ ha⟩
    · exact ⟨le_rfl,hW.le⟩
  have hmass : (∑ a,r a)=∑ e ∈ M,(w e : ℝ) := witnessMass_total label hi M w hMG
  have hbad : (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (∑ e ∈ actualSurvivingWitness hn cfg batch label M π,(w e : ℝ)) <
        (1-2*ρ)*(∑ e ∈ M,(w e : ℝ)))) ⊆
      Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
        2*ρ*(∑ a,r a)≤∑ a ∈ (positions k).image π,r a) := by
    intro π hπ
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hb := (Finset.mem_filter.mp hπ).2
    rw [actualSurvivingWitness_weight hn cfg batch label hi M w π] at hb
    have hsub : (positions (acquisitionStop hn cfg batch π)).image π ⊆ (positions k).image π :=
      Finset.image_subset_image (positions_mono (acquisitionStop_progress hn cfg batch π))
    have hinc := RandomOrderMatching.Probability.PrefixMoments.adaptive_prefix_weight_le _ _ r hsub
      (fun a _ => (hr a).1)
    change (∑ a ∈ (positions (acquisitionStop hn cfg batch π)).image π,r a)≤_ at hinc
    change (∑ e ∈ M,(w e : ℝ))-(∑ a ∈ (positions (acquisitionStop hn cfg batch π)).image π,r a)<_ at hb
    rw [hmass]
    linarith
  have hk : (positions (n:=n) k).card=k := positions_card (show k≤n from hfit)
  have ht := prefix_twice_mean_tail (positions (n:=n) k) (by simpa using hn) r W ρ hW hρ hr
    (by simpa only [hk,Fintype.card_fin] using hfrac)
  rw [hmass] at ht
  have hc : ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (∑ e ∈ actualSurvivingWitness hn cfg batch label M π,(w e : ℝ)) <
        (1-2*ρ)*(∑ e ∈ M,(w e : ℝ)))).card : ℝ) ≤
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
        2*ρ*(∑ a,r a)≤∑ a ∈ (positions k).image π,r a)).card := by
    exact_mod_cast Finset.card_le_card hbad
  rw [hmass] at hc
  exact (div_le_div_of_nonneg_right hc (by positivity)).trans ht

/-- The final-paper benchmark: the surviving portion of the fixed original
optimum, with the original input optimum on both sides of the tail estimate. -/
theorem actual_fixed_optimum_survivor_preserved {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (label : Fin n → Edge O) (hi : Function.Injective label)
    (M : Graph O) (hMG : M ⊆ Finset.univ.image label) (w : Edge O → ℕ)
    (hopt : (∑ e ∈ M,(w e : ℝ))=opt (fun e => (w e : ℝ)) (Finset.univ.image label))
    (W ρ : ℝ) (hW : 0<W) (hρ : 0≤ρ)
    (hw : ∀ e ∈ Finset.univ.image label,(w e : ℝ)≤W)
    (hfit : operationBound (V:=V) cfg.beta*cfg.epochLength≤n)
    (hfrac : ((operationBound (V:=V) cfg.beta*cfg.epochLength : ℕ) : ℝ)/n≤ρ) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (∑ e ∈ actualSurvivingWitness hn cfg model.copies label M π,(w e : ℝ)) <
        (1-2*ρ)*opt (fun e => (w e : ℝ)) (Finset.univ.image label))).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin n)) ≤
        Real.exp (-ρ*opt (fun e => (w e : ℝ)) (Finset.univ.image label)/(3*W)) := by
  have hh := actual_fixed_witness_preserved hn cfg model.copies label hi M hMG w W ρ hW hρ
    (fun e he => hw e (hMG he)) hfit hfrac
  simpa only [hopt] using hh

end RandomOrderMatching.Acquisition.Probability
