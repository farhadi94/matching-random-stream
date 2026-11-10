import RobustMatching.R8FixedHostAcquisition
import RobustMatching.R8FixedHostEligibilityCanonical

/-! Complete fixed-host suffix theorem for the actual canonical algorithm.
The copied benchmark, underfull store, parent map, cut, minimum cover,
probability experiment, and phase embeddings are all constructed here. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
open Classical MeasureTheory
open scoped BigOperators
namespace RobustMatching.R8FixedHost
open R2Cut R7SupportFlowMap R8BalancedCut R8PhaseEmbedding
open R7WeightedPhaseAssembly R8PermutationClock R8Acquisition
open R8FixedHostBenchmark R8FixedHostEligibility
variable {V B : Type*} [Fintype V] [LinearOrder V] [Fintype B]

def lowerThreshold (W L : ℕ) : ℕ := (10^30-10^21)*W*L

theorem lowerThreshold_real (W L : ℕ) :
    (lowerThreshold W L:ℝ)=(1-1/10^9:ℝ)*beta0 W L := by
  norm_num [lowerThreshold,beta0]
  ring

/-- The actual matching returned by the concrete original-edge phase bank
on a uniformly ordered physical suffix. The only reference assumptions
are canonical prior provenance and the acquisition degree upper bound.
The benchmark is any fixed original matching contained in that suffix. -/
theorem canonical_uniform_suffix {n W L : ℕ}
    (hW : 1 ≤ W) (hL : 1 ≤ L) (original : B → Edge V) (e : Fin n≃B)
    (w : Edge V → ℕ) (hw : ∀f,w f ≤ W) (fallback : Edge V)
    (prior : List (Edge V)) (H : Graph (V×Fin W))
    (hprovenance : H⊆seenCopies (canonicalCopies W w hw) prior)
    (hupper : ∀f∈H,(edgeDegree H f:ℝ) ≤ beta0 W L)
    (M : Graph V) (hM : Matching M) (hMphysical : M⊆Finset.univ.image original)
    {N δ : ℝ} (hN : 2 ≤ N) (hvertices : (Fintype.card (V×Fin W):ℝ) ≤ N)
    (hδ : 0<δ) (hδ1 : δ<1) (hlog : Real.log (100*N/δ) ≤ L) :
    (uniformOrder n).real {σ |
      outputValue w (referenceParents (canonicalParent W fallback) H)
        (eligibleOriginal (lowerThreshold W L) H (canonicalCopies W w hw))
        (suffixStream original e σ) (R8StreamingWrapper.reachedCuts n)<
      ((R7ReductionCertificate.Concrete.target:ℝ)-1/10000000)*(∑f∈M,(w f:ℝ))} ≤ 7*δ/100 := by
  let suffix := suffixStream original e (Equiv.refl _)
  let MC := copiedBenchmark W w hw M
  let A := availableSuffix (lowerThreshold W L) H (canonicalCopies W w hw) suffix
  let parent := canonicalParent W fallback
  let H0 := referenceParents parent H
  let eligible := eligibleOriginal (lowerThreshold W L) H (canonicalCopies W w hw)
  have hsub : M⊆suffix.toFinset := by
    rw [suffixStream_toFinset]
    exact hMphysical
  have hm := copiedBenchmark_exact M hM W w hw
  have hHcopies := canonical_partial_consistent W w hw fallback prior H hprovenance
  have hAcopies := canonical_available_consistent W w hw fallback (lowerThreshold W L) H prior suffix hprovenance
  have hMcopies := canonical_copies_consistent W w hw fallback M.toList
  have href : ∀f∈H,parent f∈H0 := by
    intro f hf
    exact Finset.mem_image.mpr ⟨f,hf,rfl⟩
  have hav : ∀f∈A,parent f∈H0 ∨ (eligible (parent f) ∧ ∃b,original b=parent f) := by
    intro f hf
    have hh := canonical_available_parent W w hw fallback (lowerThreshold W L) H suffix hf
    rcases hh with hh|⟨hel,hs⟩
    · exact Or.inl hh
    · apply Or.inr
      refine ⟨hel,?_⟩
      have hs' : parent f∈Finset.univ.image original := by
        rw [←suffixStream_toFinset original e (Equiv.refl _)]
        exact List.mem_toFinset.mpr hs
      obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hs'
      exact ⟨b,hb⟩
  have hlo : (lowerThreshold W L:ℝ) ≤ beta0 W L := by
    rw [lowerThreshold_real]
    have hh := beta0_large W L hW hL
    nlinarith
  have havupper := availableSuffix_upper_real (lowerThreshold W L) (beta0 W L) H
    (canonicalCopies W w hw) suffix hupper hlo
  have hlower : ∀f∈MC\A,(1-1/10^9:ℝ)*beta0 W L ≤ (edgeDegree H f:ℝ) := by
    intro f hf
    have hh := canonical_benchmark_missing_lower W w hw (lowerThreshold W L) H M suffix hsub f hf
    have hc : (lowerThreshold W L:ℝ) ≤ (edgeDegree H f:ℝ) := Nat.cast_le.mpr hh
    rwa [lowerThreshold_real] at hc
  have hh := acquisition_graph_uniform_suffix hW hL original e w parent M hM MC H A (MC\A) hm.1
    hHcopies hAcopies hMcopies
    (fun f hf=>copiedBenchmark_parent_mem M W w hw fallback hf)
    (fun f hf=>copiedBenchmark_parent_in_labels M W w hw fallback original hMphysical hf)
    H0 eligible href hav Finset.subset_union_left
    (fun f hf hna=>Finset.mem_sdiff.mpr ⟨hf,hna⟩)
    hupper havupper hlower hN hvertices hδ hδ1 hlog
  have hmass : (MC.card:ℝ)=∑f∈M,(w f:ℝ) := by
    exact_mod_cast hm.2
  rw [hmass] at hh
  exact hh

end RobustMatching.R8FixedHost
