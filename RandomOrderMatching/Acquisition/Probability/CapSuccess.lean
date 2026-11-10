import RandomOrderMatching.Acquisition.Probability.RecordCount
import RandomOrderMatching.Acquisition.Probability.StopBound
import RandomOrderMatching.Acquisition.FreezeObservation

/-! Actual cap success of the executed acquisition. The proof identifies
the executed first empty epoch and bounds its entire potential suffix store. -/
noncomputable section
open scoped BigOperators
open Classical
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition
open RandomOrderMatching.Probability.Permutation RandomOrderMatching.Probability.Stopping
variable {V : Type*} [Fintype V] [DecidableEq V]

def potentialSuffixRecords {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (π : Equiv.Perm (Fin n)) : Finset (Edge V × ℕ) :=
  let t := acquisitionStop hn cfg model.copies π
  recordsFrom cfg.lower (actualReference hn cfg model.copies π t) model.copies t
    ((List.ofFn π).drop t)

theorem actual_freeze_exists {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (π : Equiv.Perm (Fin n))
    (hfit : operationBound (V:=V) cfg.beta*cfg.epochLength≤n) :
    (stateAt cfg batch (permutationStream hn π) n).freezeAt=
      some (acquisitionStop hn cfg batch π) := by
  have hh := run_frozen_by cfg batch (inputPrefix (permutationStream hn π) n)
    (by simpa [inputPrefix] using hfit)
  change (stateAt cfg batch (permutationStream hn π) n).freezeAt≠none at hh
  cases hs : (stateAt cfg batch (permutationStream hn π) n).freezeAt with
  | none => exact (hh hs).elim
  | some t => simp [acquisitionStop,hs]

theorem actual_empty_epoch_misses {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (π : Equiv.Perm (Fin n)) (j : ℕ)
    (hall : ∀ i<cfg.epochLength,∀ e∈batch (permutationStream hn π (j*cfg.epochLength+i)),
      ¬insertable cfg.lower (actualReference hn cfg batch π (j*cfg.epochLength)) e) :
    Disjoint ((epochPositions (n:=n) cfg.epochLength j).image π)
      (actualBadParents hn cfg batch (j*cfg.epochLength) π) := by
  apply Finset.disjoint_left.mpr
  intro a ha hbad
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
  have hbounds : i.val<(j+1)*cfg.epochLength ∧ ¬i.val<j*cfg.epochLength := by
    simpa only [epochPositions,positions,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hd : i.val-j*cfg.epochLength<cfg.epochLength := by
    rw [Nat.add_mul,Nat.one_mul] at hbounds
    omega
  have hid : j*cfg.epochLength+(i.val-j*cfg.epochLength)=i.val := by omega
  obtain ⟨e,he,hins⟩ := (Finset.mem_filter.mp hbad).2
  have hstream : permutationStream hn π (j*cfg.epochLength+(i.val-j*cfg.epochLength))=π i := by
    rw [hid,permutationStream_apply hn π i.val i.isLt]
  have hh := hall (i.val-j*cfg.epochLength) hd
  rw [hstream] at hh
  exact hh e he hins

theorem suffix_records_fit_outside_bad_epochs {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (π : Equiv.Perm (Fin n)) (Γ : ℕ)
    (hfit : operationBound (V:=V) cfg.beta*cfg.epochLength≤n)
    (hgood : π ∉ badEpochUnion cfg.epochLength (operationBound (V:=V) cfg.beta) Γ
      (fun j => actualBadParents hn cfg model.copies (j*cfg.epochLength))) :
    (potentialSuffixRecords hn cfg model π).card ≤ model.kappa*Γ := by
  let t := acquisitionStop hn cfg model.copies π
  have hf := actual_freeze_exists hn cfg model.copies π hfit
  obtain ⟨j,hj,ht,hH,hall⟩ := actual_empty_epoch cfg model.copies (permutationStream hn π) n t hf
  have htk : t≤n := acquisitionStop_le hn cfg model.copies π
  have hstart : j*cfg.epochLength≤t := by rw [ht,Nat.add_mul,Nat.one_mul]; omega
  have hfreeze := actual_freeze_restrict cfg model.copies (permutationStream hn π) t n t htk le_rfl hf
  have hHstart : actualReference hn cfg model.copies π t=
      actualReference hn cfg model.copies π (j*cfg.epochLength) := by
    have hfinal : (stateAt cfg model.copies (permutationStream hn π) n).ref=
        (stateAt cfg model.copies (permutationStream hn π) t).ref := by
      have hs := stateAt_add cfg model.copies (permutationStream hn π) t (n-t)
      rw [show t+(n-t)=n by omega] at hs
      rw [hs]
      exact frozen_run_ref cfg model.copies _ _ (by rw [hfreeze]; simp)
    exact hfinal.symm.trans hH
  have hmiss := actual_empty_epoch_misses hn cfg model.copies π j hall
  have hcount : (actualBadParents hn cfg model.copies (j*cfg.epochLength) π).card≤Γ := by
    by_contra hh
    apply hgood
    apply Finset.mem_biUnion.mpr
    refine ⟨j,Finset.mem_range.mpr hj,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.lt_of_not_ge hh,hmiss⟩
  have hnd : ((List.ofFn π).drop t).Nodup :=
    List.Pairwise.sublist (List.drop_sublist _ _) (List.nodup_ofFn.mpr π.injective)
  have hparents : ∀ a∈(List.ofFn π).drop t,∀ e∈model.copies a,
      edgeDegree (actualReference hn cfg model.copies π t) e<cfg.lower →
        a∈actualBadParents hn cfg model.copies (j*cfg.epochLength) π := by
    intro a ha e he hd
    have hrem := (ofFn_drop_mem_remaining π t a).mp ha
    have hrem0 : a∈remaining (positions (j*cfg.epochLength)) π := by
      apply mem_remaining.mpr
      intro hs
      exact mem_remaining.mp hrem ((Finset.image_subset_image (positions_mono hstart)) hs)
    apply (actual_underfull_iff_bad_parent hn cfg model π _ (hstart.trans htk) a hrem0).mpr
    exact ⟨e,he,by simpa only [hHstart] using hd⟩
  have hb := actual_records_parent_bound model cfg.lower
    (actualReference hn cfg model.copies π t) t ((List.ofFn π).drop t) hnd
    (actualBadParents hn cfg model.copies (j*cfg.epochLength) π) hparents
  exact hb.trans (Nat.mul_le_mul_left model.kappa hcount)

theorem actual_final_split {n : ℕ} (hn : 0<n) (cfg : Config)
    (batch : Fin n → List (Edge V)) (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t≤n) :
    stateAt cfg batch (permutationStream hn π) n=
      runFrom cfg batch (stateAt cfg batch (permutationStream hn π) t) ((List.ofFn π).drop t) := by
  have hfull : inputPrefix (permutationStream hn π) n=List.ofFn π := by
    rw [permutation_inputPrefix hn π n le_rfl]
    simp
  have hpre := permutation_inputPrefix hn π t ht
  have hsplit := runFrom_append cfg batch (initialState : State V)
    ((List.ofFn π).take t) ((List.ofFn π).drop t)
  rw [List.take_append_drop] at hsplit
  simpa only [stateAt,run,hfull,hpre] using hsplit

/-- On the actual good acquisition event, the implemented capped collector
does not abort and stores every eligible copied suffix record exactly. -/
theorem actual_cap_survival {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (π : Equiv.Perm (Fin n)) (Γ : ℕ)
    (hfit : operationBound (V:=V) cfg.beta*cfg.epochLength≤n)
    (hcap : model.kappa*Γ≤cfg.uCap)
    (hgood : π ∉ badEpochUnion cfg.epochLength (operationBound (V:=V) cfg.beta) Γ
      (fun j => actualBadParents hn cfg model.copies (j*cfg.epochLength))) :
    (stateAt cfg model.copies (permutationStream hn π) n).aborted=false ∧
      (stateAt cfg model.copies (permutationStream hn π) n).saved=
        potentialSuffixRecords hn cfg model π := by
  let t := acquisitionStop hn cfg model.copies π
  have hf := actual_freeze_exists hn cfg model.copies π hfit
  have ht : t≤n := acquisitionStop_le hn cfg model.copies π
  have hs := actual_freeze_restrict cfg model.copies (permutationStream hn π) t n t ht le_rfl hf
  have hclean := actual_freeze_state_clean cfg model.copies (permutationStream hn π) n t hf
  have hrecords := (suffix_records_fit_outside_bad_epochs hn cfg model π Γ hfit hgood).trans hcap
  have hb : ((stateAt cfg model.copies (permutationStream hn π) t).saved ∪
      recordsFrom cfg.lower (stateAt cfg model.copies (permutationStream hn π) t).ref
        model.copies (stateAt cfg model.copies (permutationStream hn π) t).time
        ((List.ofFn π).drop t)).card ≤ cfg.uCap := by
    rw [hclean.1,Finset.empty_union,stateAt_time]
    exact hrecords
  have hh := frozen_run_complete cfg model.copies
    (stateAt cfg model.copies (permutationStream hn π) t) ((List.ofFn π).drop t)
    (by rw [hs]; simp) hclean.2 hb
  rw [actual_final_split hn cfg model.copies π t ht,hh]
  constructor
  · exact hclean.2
  · change (stateAt cfg model.copies (permutationStream hn π) t).saved ∪ _ = _
    rw [hclean.1,Finset.empty_union,stateAt_time]
    rfl

/-- Success probability for the actual hard-cap implementation. No desired
success event, historical classifier, or freeze-prefix bound is an assumption. -/
theorem actual_cap_failure_probability {n : ℕ} (hn : 0<n) (cfg : Config)
    (model : BatchModel (Fin n) V) (Γ : ℕ)
    (hfit : operationBound (V:=V) cfg.beta*cfg.epochLength≤n)
    (hcap : model.kappa*Γ≤cfg.uCap) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (stateAt cfg model.copies (permutationStream hn π) n).aborted=true)).card : ℝ) /
        Fintype.card (Equiv.Perm (Fin n)) ≤
      operationBound (V:=V) cfg.beta*Real.exp (-(cfg.epochLength : ℝ)*Γ/n) := by
  have hsub : (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (stateAt cfg model.copies (permutationStream hn π) n).aborted=true)) ⊆
      badEpochUnion cfg.epochLength (operationBound (V:=V) cfg.beta) Γ
        (fun j => actualBadParents hn cfg model.copies (j*cfg.epochLength)) := by
    intro π hπ
    by_contra hg
    have hh := (actual_cap_survival hn cfg model π Γ hfit hcap hg).1
    have ht := (Finset.mem_filter.mp hπ).2
    rw [hh] at ht
    cases ht
  have hc : ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (stateAt cfg model.copies (permutationStream hn π) n).aborted=true)).card : ℝ) ≤
      (badEpochUnion cfg.epochLength (operationBound (V:=V) cfg.beta) Γ
        (fun j => actualBadParents hn cfg model.copies (j*cfg.epochLength))).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact (div_le_div_of_nonneg_right hc (by positivity)).trans
    (actual_bad_epoch_union_bound hn cfg model.copies (operationBound (V:=V) cfg.beta) Γ hfit)

end RandomOrderMatching.Acquisition.Probability
