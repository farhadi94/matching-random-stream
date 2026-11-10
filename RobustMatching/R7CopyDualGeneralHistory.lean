import RobustMatching.R7CopyDualLiftingVerified
import RobustMatching.R2CutExchange

/-! Automatic chronological processing of an arbitrary matching with
individual observation times. The caller supplies no release schedule. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace RobustMatching.R7CopyDualGeneralHistory
open RobustMatching.R2Cut RobustMatching.R7AlgebraPath
open RobustMatching.R6FableImportance RobustMatching.R7CopyDualHistorical
open RobustMatching.R7AlgebraInterpretation
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem covered_erase_of_matching {T : Graph V} (hT : Matching T)
    (e : Edge V) (he : e ∈ T) : covered (T.erase e) = covered T \ e.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨f,hf,hvf⟩ := mem_covered.mp hv
    obtain ⟨hne,hfT⟩ := Finset.mem_erase.mp hf
    refine Finset.mem_sdiff.mpr ⟨mem_covered.mpr ⟨f,hfT,hvf⟩,?_⟩
    intro hve
    exact Finset.disjoint_left.mp (hT hfT he hne) hvf hve
  · intro hv
    obtain ⟨hvT,hve⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨f,hf,hvf⟩ := mem_covered.mp hvT
    have hne : f ≠ e := by intro h; subst f; exact hve hvf
    exact mem_covered.mpr ⟨f,Finset.mem_erase.mpr ⟨hne,hf⟩,hvf⟩

/-- Observe each matching edge at an arbitrary individual historical time.
The proof selects the earliest remaining time and constructs the legal
release order. Initial observations and repeated times are allowed. -/
theorem historical_observed_matching
    (w : Edge V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (K : ℕ → Graph V) (hK : ∀ i j, i ≤ j → K i ⊆ K j)
    (n : ℕ) (clock : Edge V → ℕ) (T : Graph V) (s : ℕ)
    (hsn : s ≤ n) (hT : Matching T)
    (hstart : ∀ e ∈ T, s ≤ clock e)
    (hend : ∀ e ∈ T, clock e ≤ n)
    (hclosed : ∀ e ∈ T, opt w (insert e (K (clock e))) = opt w (K (clock e))) :
    (∑ e ∈ T, w e) + pathValue w (K s) (covered T) ≤ 2 * opt w (K n) := by
  induction T using Finset.strongInductionOn generalizing s with
  | _ T ih =>
    by_cases hne : T.Nonempty
    · obtain ⟨e,he,hmin⟩ := T.exists_min_image clock hne
      have herase : T.erase e ⊂ T := Finset.erase_ssubset he
      have hh := ih (T.erase e) herase (clock e) (hend e he)
        (matching_mono hT (Finset.erase_subset _ _))
        (fun f hf => hmin f (Finset.mem_of_mem_erase hf))
        (fun f hf => hend f (Finset.mem_of_mem_erase hf))
        (fun f hf => hclosed f (Finset.mem_of_mem_erase hf))
      have hp := closed_edge_price w (K (clock e)) e (hclosed e he)
      have hs := pathValue_release w (K (clock e))
        (pathValue_submodular_real _ _ hw) (covered T) e.val
        (fun v hv => mem_covered.mpr ⟨e,he,hv⟩)
      have hm := pathValue_host_mono w (hK s (clock e) (hstart e he)) (covered T)
      rw [← covered_erase_of_matching hT e he] at hs
      have hsum := Finset.sum_erase_add T w he
      linarith
    · have hempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst T
      have hm := RobustMatching.Lower.packingOpt_mono Matching empty_matching w (hK s n hsn)
      simp only [Finset.sum_empty,covered,Finset.biUnion_empty,pathValue_empty,zero_add]
      change opt w (K s) ≤ opt w (K n) at hm
      linarith

/-- Any individually closed proposal graph can be tested through the
matchings selected by a two-layer auxiliary graph. -/
theorem historical_every_matching
    (w : Edge V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (K : ℕ → Graph V) (hK : ∀ i j, i ≤ j → K i ⊆ K j)
    (n : ℕ) (P : Graph V)
    (hclosed : ∀ e ∈ P, ∃ t ≤ n, opt w (insert e (K t)) = opt w (K t))
    (T : Graph V) (hTP : T ⊆ P) (hT : Matching T) :
    (∑ e ∈ T, w e) + pathValue w (K 0) (covered T) ≤ 2 * opt w (K n) := by
  classical
  let clock : Edge V → ℕ := fun e => if h : e ∈ P then (hclosed e h).choose else 0
  apply historical_observed_matching w hw K hK n clock T 0 (Nat.zero_le _) hT
  · intro e he; exact Nat.zero_le _
  · intro e he
    simpa [clock,hTP he] using (hclosed e (hTP he)).choose_spec.1
  · intro e he
    simpa [clock,hTP he] using (hclosed e (hTP he)).choose_spec.2

end RobustMatching.R7CopyDualGeneralHistory

#print axioms RobustMatching.R7CopyDualGeneralHistory.historical_every_matching
