import RandomOrderMatching.Acquisition.Probability.HistoryIntegration
import RandomOrderMatching.Analysis.FixedHost.CanonicalGuarantee

/-! The unconditional physical-suffix failure estimate for the actual
canonical acquisition. The fixed-host theorem supplies the local bound;
all acquisition histories, graph invariants, and benchmark interfaces are
constructed from the execution. -/
noncomputable section
open Classical
open scoped BigOperators
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Streaming
open RandomOrderMatching.Probability.Stopping RandomOrderMatching.Probability.Permutation
open RandomOrderMatching.Phases.Execution RandomOrderMatching.Probability.ClockCoupling
open RandomOrderMatching.Analysis.FixedHost RandomOrderMatching.Analysis.FixedHost.Eligibility RandomOrderMatching.Analysis.BalancedCut
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Actual original-label permutation failure, with no supplied stopping,
cap-success, graph embedding, copied benchmark, or conditional suffix premise.
The only configuration conditions identify the canonical degree thresholds. -/
theorem canonical_physical_suffix_failure_probability {n W L : ℕ}
    (hn : 0<n) (hW : 1≤W) (hL : 1≤L)
    (cfg : Config) (hbeta : (cfg.beta:ℝ)≤beta0 W L)
    (hlower : cfg.lower=lowerThreshold W L)
    (w : Edge V→ℕ) (hw : ∀e,w e≤W) (fallback : Edge V)
    (label : Fin n→Edge V) (M : Graph V) (hM : Matching M)
    (hMG : M⊆Finset.univ.image label)
    {N δ : ℝ} (hN : 2≤N) (hvertices : (Fintype.card (V×Fin W):ℝ)≤N)
    (hδ : 0<δ) (hδ1 : δ<1) (hlog : Real.log (100*N/δ)≤L) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      physicalSuffixValue w cfg (canonicalBatchModel W w hw fallback) (labelledStream label π)<
        ((RandomOrderMatching.Certificates.DegreeProfile.Concrete.target:ℝ)-1/10000000)*
          (∑f∈survivingFixedMatching cfg (canonicalBatchModel W w hw fallback)
            (labelledStream label π) M,(w f:ℝ)))).card : ℝ)/
      Fintype.card (Equiv.Perm (Fin n))≤7*δ/100 := by
  apply physical_suffix_failure_from_fixed_hosts hn w cfg (canonicalBatchModel W w hw fallback) label M
  intro σ
  let batch := fun i => canonicalCopies W w hw (label i)
  let t := acquisitionStop hn cfg batch σ
  have ht : t≤n := acquisitionStop_le hn cfg batch σ
  let H := actualReference hn cfg batch σ t
  let prior := (labelledStream label σ).take t
  let original : remaining (positions t) σ → Edge V := fun a => label a.val
  let e := suffixEnumeration σ t ht
  let Ms := actualSurvivingWitness hn cfg batch label M σ
  have hstate := labelled_prefix_state hn cfg (canonicalCopies W w hw) label σ t ht
  have href : (run cfg (canonicalCopies W w hw) prior).ref=H := congrArg State.ref hstate
  have hprovenance : H⊆seenCopies (canonicalCopies W w hw) prior := by
    rw [←href]
    exact run_ref_subset cfg (canonicalCopies W w hw) prior
  have hupper : ∀f∈H,(edgeDegree H f:ℝ)≤beta0 W L := by
    rw [←href]
    intro f hf
    have hh := run_upper cfg (canonicalCopies W w hw) prior f hf
    exact (Nat.cast_le.mpr hh).trans hbeta
  have hMs : Matching Ms := (actualSurvivingWitness_spec hn cfg batch label M hM hMG σ).1
  have hphysical : Ms⊆Finset.univ.image original := by
    intro f hf
    have hpair := Finset.mem_sdiff.mp hf
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp (hMG hpair.1)
    have hrem : a∈remaining (positions t) σ := by
      apply mem_remaining.mpr
      intro hseen
      exact hpair.2 (he ▸ Finset.mem_image_of_mem label hseen)
    exact Finset.mem_image.mpr ⟨⟨a,hrem⟩,Finset.mem_univ _,he⟩
  have hh := canonical_uniform_suffix hW hL original e w hw fallback prior H hprovenance hupper
    Ms hMs hphysical hN hvertices hδ hδ1 hlog
  have hel : eligibleOriginal (lowerThreshold W L) H (canonicalCopies W w hw)=
      (fun a => ∃f∈canonicalCopies W w hw a,edgeDegree H f<lowerThreshold W L) := rfl
  rw [hel] at hh
  simp only [historySuffixEvent,canonicalBatchModel,hlower]
  convert hh using 1
  rfl

end RandomOrderMatching.Acquisition.Probability
