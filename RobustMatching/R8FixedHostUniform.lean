import RobustMatching.R8FixedHostAnalytic
import RobustMatching.R8PermutationClockTransfer
import RobustMatching.R8StreamingWrapperBracket

/-! Transfer of the unconditional analytic repair bound to the uniform
physical suffix order. The comparison with the algorithm is required only
on the actual count bracket, and no conditioning is imposed on repair. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical MeasureTheory
namespace RobustMatching.R8FixedHost
open R8RepairProbability R7ClosedRepair.Typed R8PermutationClock
variable {B G M P I J R U : Type*}
variable [Fintype B] [Fintype G] [Fintype M] [Fintype P]
  [Fintype I] [Fintype J] [Fintype R] [Fintype U]
variable (D : LocalData (B:=B) (G:=G) (M:=M) (P:=P) (I:=I) (J:=J) (R:=R) (U:=U))

theorem uniform_analytic_comparison {n : ℕ} (e : Fin n≃B)
    (value : Equiv.Perm (Fin n)→ℝ) (c : ℕ) {r μ δ t : ℝ}
    (hn : 0<n) (ht : 0<t)
    (hleft : alpha*n+t≤c) (hright : (c:ℝ)≤omega*n-t)
    (hrepair : (experiment (B:=B)).real
      {z | analyticValue D z<r*μ}≤δ)
    (hcomparison : ∀s,cutoffBracket c (coupledClocks s)→
      analyticValue D (labeledClocks e s)≤value (coupledOrder s)) :
    (uniformOrder n).real {σ | value σ<r*μ}≤δ+2*Real.exp (-2*t^2/n) := by
  apply uniform_stream_bad_bound e {σ | value σ<r*μ}
    {z | r*μ≤analyticValue D z} c hn ht hleft hright
  · simpa only [Set.compl_ofPred,not_le] using hrepair
  · intro s hs hb hv
    exact not_lt_of_ge (hs.trans (hcomparison s hb)) hv

theorem uniform_profile_ratio {n : ℕ} (e : Fin n≃B)
    (value : Equiv.Perm (Fin n)→ℝ) (c : ℕ) {r μ N θ L t : ℝ}
    (hn : 0<n) (ht : 0<t)
    (hleft : alpha*n+t≤c) (hright : (c:ℝ)≤omega*n-t)
    (hμ : 0<μ) (hN : 1≤N) (hμN : μ≤N) (hθ : 0<θ) (hθsmall : θ≤1/100)
    (hL : 0<L) (hscale : Real.exp (-L)≤θ/N)
    (hbeta : 10^30*(D.kappa:ℝ)*L/2≤D.beta) (hmuBeta : (49:ℝ)/100*D.beta≤μ)
    (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hcount : randomPairCount G M J R≤μ)
    (hblock : ∀b,originalMultiplicity D.parents b≤D.kappa)
    (hcertificate : r*μ≤max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w))
    (hcomparison : ∀s,cutoffBracket c (coupledClocks s)→
      analyticValue D (labeledClocks e s)≤value (coupledOrder s)) :
    (uniformOrder n).real {σ | value σ<(r-1/10000000)*μ}≤
      5*θ+2*Real.exp (-2*t^2/n) :=
  uniform_analytic_comparison D e value c hn ht hleft hright
    (analytic_ratio_failure D hμ hN hμN hθ hθsmall hL hscale hbeta hmuBeta
      hcenters hcount hblock hcertificate) hcomparison

theorem uniform_selected_phase_ratio {n : ℕ} (e : Fin n≃B)
    (value : Equiv.Perm (Fin n)→ℝ) {r μ N θ L : ℝ}
    (hn : 10000000≤n)
    (hμ : 0<μ) (hN : 1≤N) (hμN : μ≤N) (hθ : 0<θ) (hθsmall : θ≤1/100)
    (hL : 0<L) (hscale : Real.exp (-L)≤θ/N)
    (hbeta : 10^30*(D.kappa:ℝ)*L/2≤D.beta) (hmuBeta : (49:ℝ)/100*D.beta≤μ)
    (hcenters : (Fintype.card (Centers G M P I J):ℝ)≤μ)
    (hcount : randomPairCount G M J R≤μ)
    (hblock : ∀b,originalMultiplicity D.parents b≤D.kappa)
    (hcertificate : r*μ≤max (Fintype.card (Centers G M P I J):ℝ)
      (profile alpha omega D.w))
    (hcomparison : ∀s,cutoffBracket (R8StreamingWrapper.selectedCutoff n) (coupledClocks s)→
      analyticValue D (labeledClocks e s)≤value (coupledOrder s)) :
    (uniformOrder n).real {σ | value σ<(r-1/10000000)*μ}≤
      5*θ+2*Real.exp (-(n:ℝ)/8000000000000) := by
  have hnpos : 0<n := by omega
  have hnr : 0<(n:ℝ) := Nat.cast_pos.mpr hnpos
  obtain ⟨hl,hu⟩ := R8StreamingWrapper.selected_cutoff_clock_bracket hn
  have h := uniform_profile_ratio D e value (R8StreamingWrapper.selectedCutoff n)
    hnpos (show (0:ℝ)<n/4000000 by positivity)
    (by simpa [alpha] using hl) (by simpa [omega] using hu)
    hμ hN hμN hθ hθsmall hL hscale hbeta hmuBeta hcenters hcount hblock
    hcertificate hcomparison
  have he : -2*((n:ℝ)/4000000)^2/n=-(n:ℝ)/8000000000000 := by field_simp; ring
  simpa only [he] using h

end RobustMatching.R8FixedHost
