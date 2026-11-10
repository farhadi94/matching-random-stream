import RobustMatching.R8FixedHostExecution
import RobustMatching.R8FixedHostParents
import RobustMatching.R8FixedHostDensity
import RobustMatching.R8FixedHostNumerics

/-! Actual fixed-cut, uniform-physical-suffix guarantee. All repair and
phase-comparison hypotheses are derived from finite graph/parent data.
The large-instance branch and physical suffix length are proved internally. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
open Classical MeasureTheory
open scoped BigOperators
namespace RobustMatching.R8FixedHost
open R2Cut R7SupportFlowMap R7ClosedRepair.TypedLabeling R8RepairProbability
open R7ClosedRepair.Typed R8PermutationClock R7WeightedPhaseAssembly R8PhaseEmbedding
open R7GraphBipartiteExchange
variable {V B : Type*} [Fintype V] [LinearOrder V] [Fintype B]

theorem fixed_cut_uniform_suffix
    {n W : ℕ} (hW : 0<W) (original : B → Edge V) (e : Fin n≃B)
    (w : Edge V → ℕ) (parent : Edge (V×Fin W) → Edge V)
    (MC H A : Graph (V×Fin W)) (hMC : Matching MC) (C : Finset (V×Fin W))
    (H0 : Graph V) (eligible : Edge V → Prop) (cut : Finset V)
    (hHcross : Crosses H (copyCut cut W)) (hAcross : Crosses A (copyCut cut W))
    (hMcross : Crosses MC (copyCut cut W))
    (hHcopies : ConsistentCopies W w parent H) (hAcopies : ConsistentCopies W w parent A)
    (hMcopies : ConsistentCopies W w parent MC)
    (href : ∀f∈H,parent f∈H0)
    (hav : ∀f∈A,parent f∈H0 ∨ (eligible (parent f) ∧ ∃b,original b=parent f))
    (hphysical : ∀f∈MC,∃b,original b=parent f)
    (hminimum : rank A=C.card) (beta : ℝ) (hbeta : 0<beta)
    (hcover : ∀f∈H,∃v∈f.val,v∈C)
    (hupper : ∀f∈H,incidenceDegree H (orientedEndpoint C f 0)+
      incidenceDegree H (orientedEndpoint C f 1) ≤ beta)
    (hpairLower : ∀f∈MC,actualPairKind C A f=.root ∨ actualPairKind C A f=.missing ∨
      actualPairKind C A f=.internalMissing → beta*(1-(R7ReductionCertificate.Concrete.data.lam:ℝ)) ≤ 
      incidenceDegree H (orientedEndpoint C f 0)+incidenceDegree H (orientedEndpoint C f 1))
    (hpairUpper : ∀f∈MC,actualPairKind C A f=.internalAvailable → 
      incidenceDegree H (orientedEndpoint C f 0)+incidenceDegree H (orientedEndpoint C f 1) ≤ beta)
    {N θ L : ℝ} (hN : 2 ≤ N) (hvertices : (Fintype.card (V×Fin W):ℝ) ≤ N)
    (hθ : 0<θ) (hθsmall : θ ≤ 1/100) (hL : 1 ≤ L)
    (hscale : Real.exp (-L) ≤ θ/N) (hsize : 10^30*(W:ℝ)*L/2 ≤ beta) :
    (uniformOrder n).real {σ |
      outputValue w H0 eligible (suffixStream original e σ) (R8StreamingWrapper.reachedCuts n)<
      ((R7ReductionCertificate.Concrete.target:ℝ)-1/10000000)*(MC.card:ℝ)} ≤ 7*θ := by
  let value := fun σ=>outputValue w H0 eligible (suffixStream original e σ) (R8StreamingWrapper.reachedCuts n)
  let r : ℝ := (R7ReductionCertificate.Concrete.target:ℝ)-1/10000000
  have hbase (σ) : (C.card:ℝ) ≤ value σ :=
    actual_base_le_output W MC H A hMC C beta original e w parent H0 eligible cut hAcross hAcopies hav hminimum σ
  have hmuNonneg : (0:ℝ) ≤ MC.card := Nat.cast_nonneg _
  by_cases hbig : (714:ℝ)/1000*MC.card ≤ C.card
  · have hs : {σ | value σ<r*(MC.card:ℝ)}=∅ := by
      ext σ
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      apply not_lt_of_ge
      exact (mul_le_mul_of_nonneg_right (le_of_lt target_below_base_branch) hmuNonneg).trans
        (hbig.trans (hbase σ))
    change (uniformOrder n).real {σ | value σ<r*(MC.card:ℝ)} ≤ 7*θ
    rw [hs]
    simp only [measureReal_empty]
    positivity
  have hsmall : C.card<MC.card := by
    have hh : (C.card:ℝ)<MC.card := by nlinarith
    exact Nat.cast_lt.mp hh
  have hμ : 0<MC.card := Nat.lt_of_le_of_lt (Nat.zero_le _) hsmall
  have hμr : (0:ℝ)<MC.card := Nat.cast_pos.mpr hμ
  let bin := actualDegreeBin H beta
  let mask := actualMinimumMask MC hMC C A bin H beta
  have hmuBeta : (49:ℝ)/100*beta ≤ MC.card := by
    apply deficient_benchmark_large MC H hMC C A bin mask beta hbeta hcover hupper
      (fun f hf hr=>?_) hsmall
    have hh := hpairLower f hf (Or.inl hr)
    convert hh using 1
    all_goals norm_num [R7ReductionCertificate.Concrete.data]
  let par := physicalParents MC original parent hphysical
  have hfiber := physicalParents_fiber_le MC hMC original parent w hMcopies hphysical
  have hparents := benchmark_card_le_parents MC par W hfiber
  have hcardB : Fintype.card B=n := by simpa using Fintype.card_congr e.symm
  rw [hcardB] at hparents
  have hlength := deficient_suffix_length hW (show 0<L by linarith) hsize hmuBeta hparents
  have hn := suffix_length_short_threshold hL hlength
  have hnpos : 0<n := by omega
  let b0 := e ⟨0,hnpos⟩
  let D := graphLocalData MC H hMC C A beta par b0 W hW hfiber
    (fun x=>originalSide cut x.1) (crosses_originalSides H cut hHcross) hbeta hcover hupper
  have hμN : (MC.card:ℝ) ≤ N :=
    (Nat.cast_le.mpr (matching_card_le_vertices MC hMC)).trans hvertices
  have hrepair := graph_analytic_ratio_failure MC H hMC C A beta par b0 W hW hfiber
    (fun x=>originalSide cut x.1) (crosses_originalSides H cut hHcross) hbeta hcover hupper
    hpairLower hpairUpper hμ (by linarith : 1 ≤ N) hμN hθ hθsmall (by linarith : 0<L)
    hscale hsize hmuBeta hsmall.le
  obtain ⟨hl,hu⟩ := R8StreamingWrapper.selected_cutoff_clock_bracket hn
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hnpos
  have hh := uniform_analytic_comparison D e value (R8StreamingWrapper.selectedCutoff n)
    hnpos (show (0:ℝ)<n/4000000 by positivity)
    (by simpa [alpha] using hl) (by simpa [omega] using hu) hrepair
    (fun s hb=>coupled_analytic_le_output W MC H A hMC C beta original e par b0 W hW hfiber
      w parent (physicalParents_identity MC original parent hphysical) H0 eligible cut
      hHcross hAcross hMcross hHcopies hAcopies hMcopies href hav hminimum hbeta hcover hupper hn s hb)
  have he : -2*((n:ℝ)/4000000)^2/n=-(n:ℝ)/8000000000000 := by field_simp; ring
  rw [he] at hh
  have hb := suffix_bracket_budget (show 1 ≤ N by linarith) hθ.le (show 0 ≤ L by linarith) hscale hlength
  exact hh.trans (by linarith)

end RobustMatching.R8FixedHost
