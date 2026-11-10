import RobustMatching.R8FixedHostMain
import RobustMatching.R8FixedHostCutInterface

/-! Construct the analytic cut and minimum cover inside the actual uniform
suffix theorem. The remaining graph inequalities are precisely the frozen
acquisition upper bound and the non-underfull lower bound. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
open Classical MeasureTheory
namespace RobustMatching.R8FixedHost
open R2Cut R7SupportFlowMap R8BalancedCut R2BalancedCut R8PhaseEmbedding
open R7WeightedPhaseAssembly R8PermutationClock R8Acquisition
variable {V B : Type*} [Fintype V] [LinearOrder V] [Fintype B]

theorem acquisition_graph_uniform_suffix {n W L : ℕ}
    (hW : 1 ≤ W) (hL : 1 ≤ L) (original : B → Edge V) (e : Fin n≃B)
    (w : Edge V → ℕ) (parent : Edge (V×Fin W) → Edge V)
    (M : Graph V) (hM : Matching M) (MC H A Nbad : Graph (V×Fin W)) (hMC : Matching MC)
    (hHcopies : ConsistentCopies W w parent H) (hAcopies : ConsistentCopies W w parent A)
    (hMcopies : ConsistentCopies W w parent MC)
    (hparentM : ∀f∈MC,parent f∈M)
    (hphysical : ∀f∈MC,∃b,original b=parent f)
    (H0 : Graph V) (eligible : Edge V → Prop)
    (href : ∀f∈H,parent f∈H0)
    (hav : ∀f∈A,parent f∈H0 ∨ (eligible (parent f) ∧ ∃b,original b=parent f))
    (hHA : H⊆A) (hmissing : ∀f∈MC,f∉A → f∈Nbad)
    (hupper : ∀f∈H,(edgeDegree H f:ℝ) ≤ beta0 W L)
    (havailable : ∀f∈A,(edgeDegree H f:ℝ) ≤ beta0 W L)
    (hlower : ∀f∈Nbad,(1-1/10^9:ℝ)*beta0 W L ≤ (edgeDegree H f:ℝ))
    {N δ : ℝ} (hN : 2 ≤ N) (hvertices : (Fintype.card (V×Fin W):ℝ) ≤ N)
    (hδ : 0<δ) (hδ1 : δ<1) (hlog : Real.log (100*N/δ) ≤ L) :
    (uniformOrder n).real {σ |
      outputValue w H0 eligible (suffixStream original e σ) (R8StreamingWrapper.reachedCuts n)<
      ((R7ReductionCertificate.Concrete.target:ℝ)-1/10000000)*(MC.card:ℝ)} ≤ 7*δ/100 := by
  obtain ⟨z,C,hmc,hcoverA,hminimum,hcoverH,hu,hl,ha⟩ :=
    actual_cut_profile_geometry (R7GraphKonig.simpleGraph (Finset.univ:Graph V)) (canonicalSymWeight w) W
      M hM MC H A Nbad
      (fun f hf=>⟨parent f,hparentM f hf,hMcopies.projection f hf⟩)
      (consistent_subgraph_unfolding w parent H hHcopies) hHA hmissing W L hW hL
      N δ hN hvertices hδ hδ1 hlog hupper havailable hlower
  let H' := restrict H (fun x=>z x.1)
  let A' := restrict A (fun x=>z x.1)
  have hβ := final_scale_positive W L hW hL
  have hh := fixed_cut_uniform_suffix (by omega : 0<W) original e w parent MC H' A' hMC C
    H0 eligible (cutSide z)
    (restricted_crosses_copyCut H z) (restricted_crosses_copyCut A z) (side_crosses_copyCut MC z hmc)
    (hHcopies.mono (restrict_subset H _)) (hAcopies.mono (restrict_subset A _)) hMcopies
    (fun f hf=>href f (restrict_subset H _ hf))
    (fun f hf=>hav f (restrict_subset A _ hf)) hphysical hminimum.symm
    (betaCut (beta0 W L)) hβ.1 hcoverH hu hl ha hN hvertices
    (show 0<δ/100 by positivity) (show δ/100 ≤ 1/100 by linarith)
    (show (1:ℝ) ≤ L by exact_mod_cast hL)
    (final_log_scale (show 0<N by linarith) hδ hlog) hβ.2
  convert hh using 1
  all_goals ring

end RobustMatching.R8FixedHost
