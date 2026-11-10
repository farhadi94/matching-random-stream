import RobustMatching.R6FableImportancePhase

/-! Actual original-edge weighted phases.  The stored graph, its optimum and
the forced-edge rule are defined here.  No performance or drift property is
assumed.  Integer weights give a hard bound on voluntarily retained records.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7WeightedPhase
open RobustMatching.R2Cut RobustMatching.Lower
open RobustMatching.R6FableImportance

variable {V : Type*} [DecidableEq V]

def natOpt (w : Edge V → ℕ) (G : Graph V) : ℕ :=
  G.powerset.sup fun M => if Matching M then ∑ e ∈ M, w e else 0

theorem matching_weight_le_natOpt (w : Edge V → ℕ) {G M : Graph V}
    (hMG : M ⊆ G) (hM : Matching M) : (∑ e ∈ M, w e) ≤ natOpt w G := by
  simpa [natOpt, hM] using
    (Finset.le_sup (f := fun M : Graph V => if Matching M then ∑ e ∈ M, w e else 0)
      (Finset.mem_powerset.mpr hMG))

theorem natOpt_le (w : Edge V → ℕ) {G : Graph V} {b : ℕ}
    (h : ∀ M ⊆ G, Matching M → (∑ e ∈ M, w e) ≤ b) : natOpt w G ≤ b := by
  apply Finset.sup_le
  intro M hM
  split_ifs with hm
  · exact h M (Finset.mem_powerset.mp hM) hm
  · exact Nat.zero_le _

theorem natOpt_attained (w : Edge V → ℕ) (G : Graph V) :
    ∃ M ⊆ G, Matching M ∧ (∑ e ∈ M, w e) = natOpt w G := by
  let ms := G.powerset.filter Matching
  have hne : ms.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    simp [Matching]
  obtain ⟨M, hM, hmax⟩ := ms.exists_max_image (fun N => ∑ e ∈ N, w e) hne
  obtain ⟨hMG, hm⟩ := Finset.mem_filter.mp hM
  have hsub := Finset.mem_powerset.mp hMG
  refine ⟨M, hsub, hm, Nat.le_antisymm (matching_weight_le_natOpt w hsub hm) ?_⟩
  apply natOpt_le
  intro N hNG hn
  exact hmax N (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hNG, hn⟩)

theorem natOpt_mono (w : Edge V → ℕ) {G H : Graph V} (h : G ⊆ H) :
    natOpt w G ≤ natOpt w H := by
  apply natOpt_le
  intro M hMG hM
  exact matching_weight_le_natOpt w (hMG.trans h) hM

theorem opt_eq_natOpt (w : Edge V → ℕ) (G : Graph V) :
    opt (fun e => (w e : ℝ)) G = (natOpt w G : ℝ) := by
  apply le_antisymm
  · obtain ⟨M, hMG, hM, hval⟩ :=
      packingOpt_attained Matching empty_matching (fun e => (w e : ℝ)) G
    change packingOpt Matching empty_matching (fun e => (w e : ℝ)) G ≤ _
    rw [hval]
    exact_mod_cast matching_weight_le_natOpt w hMG hM
  · obtain ⟨M, hMG, hM, hval⟩ := natOpt_attained w G
    have h := weight_le_packingOpt Matching empty_matching
      (fun e => (w e : ℝ)) hM hMG
    change (∑ e ∈ M, (w e : ℝ)) ≤ opt (fun e => (w e : ℝ)) G at h
    rw [← hval]
    exact_mod_cast h

/-- `forced` is a fixed class of original labels; the empty class is the
strict-gain phase, and underfull labels give the extended phase. -/
def step (w : Edge V → ℕ) (forced G : Graph V) (e : Edge V) : Graph V :=
  if e ∈ forced ∨ natOpt w G < natOpt w (insert e G) then insert e G else G

def run (w : Edge V → ℕ) (forced G : Graph V) (es : List (Edge V)) : Graph V :=
  es.foldl (step w forced) G

theorem subset_step (w : Edge V → ℕ) (forced G : Graph V) (e : Edge V) :
    G ⊆ step w forced G e := by
  unfold step
  split_ifs
  · exact Finset.subset_insert _ _
  · rfl

theorem step_subset_insert (w : Edge V → ℕ) (forced G : Graph V) (e : Edge V) :
    step w forced G e ⊆ insert e G := by
  unfold step
  split_ifs
  · rfl
  · exact Finset.subset_insert _ _

theorem natOpt_step (w : Edge V → ℕ) (forced G : Graph V) (e : Edge V) :
    natOpt w (step w forced G e) = natOpt w (insert e G) := by
  unfold step
  split_ifs with h
  · rfl
  · exact Nat.le_antisymm (natOpt_mono w (Finset.subset_insert _ _))
      (Nat.le_of_not_gt (fun hh => h (Or.inr hh)))

theorem step_gain (w : Edge V → ℕ) (forced G : Graph V) (e : Edge V) :
    opt (fun f => (w f : ℝ)) (step w forced G e) - opt (fun f => (w f : ℝ)) G =
      max 0 ((w e : ℝ) - price (fun f => (w f : ℝ)) G e) := by
  have h : opt (fun f => (w f : ℝ)) (step w forced G e) =
      opt (fun f => (w f : ℝ)) (insert e G) := by
    simp only [opt_eq_natOpt, natOpt_step]
  rw [h]
  exact insertion_gain (fun f => (w f : ℝ)) G e

theorem forced_mem_step (w : Edge V → ℕ) (forced G : Graph V) (e : Edge V)
    (he : e ∈ forced) : e ∈ step w forced G e := by
  simp [step, he]

theorem positive_gain_mem_step (w : Edge V → ℕ) (forced G : Graph V) (e : Edge V)
    (h : natOpt w G < natOpt w (insert e G)) : e ∈ step w forced G e := by
  simp [step, h]

theorem subset_run (w : Edge V → ℕ) (forced G : Graph V) (es : List (Edge V)) :
    G ⊆ run w forced G es := by
  induction es generalizing G with
  | nil => exact Finset.Subset.refl G
  | cons e es ih =>
      exact (subset_step w forced G e).trans (ih (step w forced G e))

theorem run_subset (w : Edge V → ℕ) (forced G : Graph V) (es : List (Edge V)) :
    run w forced G es ⊆ G ∪ es.toFinset := by
  induction es generalizing G with
  | nil => simp [run]
  | cons e es ih =>
      intro f hf
      have hh := ih (step w forced G e) hf
      rcases Finset.mem_union.mp hh with hs | hs
      · rcases Finset.mem_insert.mp (step_subset_insert w forced G e hs) with rfl | hg
        · simp
        · exact Finset.mem_union_left _ hg
      · exact Finset.mem_union_right _ (by simpa using Finset.mem_insert_of_mem hs)

theorem forced_mem_run (w : Edge V → ℕ) (forced G : Graph V) (es : List (Edge V))
    (e : Edge V) (he : e ∈ es) (hf : e ∈ forced) : e ∈ run w forced G es := by
  induction es generalizing G with
  | nil => simp at he
  | cons f es ih =>
      rcases List.mem_cons.mp he with rfl | he
      · exact subset_run w forced (step w forced G e) es (forced_mem_step w forced G e hf)
      · exact ih (step w forced G f) he

/-- Every voluntary new record pays an integer unit of actual weighted
optimum. Forced records are excluded because they are charged separately. -/
theorem step_record_bound (w : Edge V → ℕ) (forced G : Graph V) (e : Edge V) :
    ((step w forced G e) \ forced).card + natOpt w G ≤
      (G \ forced).card + natOpt w (step w forced G e) := by
  unfold step
  split_ifs with h
  · by_cases hf : e ∈ forced
    · have hs : insert e G \ forced = G \ forced := by
        ext f
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        aesop
      rw [hs]
      exact Nat.add_le_add_left (natOpt_mono w (Finset.subset_insert _ _)) _
    · have hg : natOpt w G < natOpt w (insert e G) := h.resolve_left hf
      have he : e ∉ G := by
        intro he
        simpa [Finset.insert_eq_of_mem he] using hg
      have hs : insert e G \ forced = insert e (G \ forced) := by
        ext f
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        aesop
      rw [hs, Finset.card_insert_of_notMem (by simp [he])]
      omega
  · exact le_refl _

theorem run_record_bound (w : Edge V → ℕ) (forced G : Graph V) (es : List (Edge V)) :
    (run w forced G es \ forced).card + natOpt w G ≤
      (G \ forced).card + natOpt w (run w forced G es) := by
  induction es generalizing G with
  | nil => exact le_refl _
  | cons e es ih =>
      have h1 := step_record_bound w forced G e
      have h2 := ih (step w forced G e)
      change (run w forced (step w forced G e) es \ forced).card + natOpt w G ≤
        (G \ forced).card + natOpt w (run w forced (step w forced G e) es)
      omega

/-- Every processed original was affordable relative to the INITIAL base
at the final optimum value. This remains true when its rejection later
revives; it is weaker than claiming final singleton closure. -/
theorem processed_initial_extension_bound (w : Edge V → ℕ)
    (forced G : Graph V) (es : List (Edge V)) (e : Edge V) (he : e ∈ es) :
    natOpt w (insert e G) ≤ natOpt w (run w forced G es) := by
  induction es generalizing G with
  | nil => simp at he
  | cons f es ih =>
      rcases List.mem_cons.mp he with rfl | he
      · have hh := natOpt_mono w (subset_run w forced (step w forced G e) es)
        rw [natOpt_step] at hh
        exact hh
      · exact (natOpt_mono w (Finset.insert_subset_insert e (subset_step w forced G f))).trans
          (ih (step w forced G f) he)

theorem natOpt_vertex_bound (w : Edge V → ℕ) (G : Graph V) (vertices : Finset V)
    (W : ℕ) (hw : ∀ e ∈ G, w e ≤ W)
    (hv : ∀ e ∈ G, e.val ⊆ vertices) : natOpt w G ≤ W * (vertices.card / 2) := by
  apply natOpt_le
  intro M hMG hM
  have hc : covered M ⊆ vertices := by
    intro v hvM
    obtain ⟨e, he, hve⟩ := mem_covered.mp hvM
    exact hv e (hMG he) hve
  have hcard : M.card ≤ vertices.card / 2 := by
    have hh := Finset.card_le_card hc
    rw [covered_card hM] at hh
    omega
  calc
    (∑ e ∈ M, w e) ≤ ∑ _e ∈ M, W := Finset.sum_le_sum (fun e he => hw e (hMG he))
    _ = W * M.card := by simp [Nat.mul_comm]
    _ ≤ W * (vertices.card / 2) := Nat.mul_le_mul_left W hcard

end RobustMatching.R7WeightedPhase

#print axioms RobustMatching.R7WeightedPhase.step_gain
#print axioms RobustMatching.R7WeightedPhase.run_record_bound
#print axioms RobustMatching.R7WeightedPhase.forced_mem_run
#print axioms RobustMatching.R7WeightedPhase.natOpt_vertex_bound
