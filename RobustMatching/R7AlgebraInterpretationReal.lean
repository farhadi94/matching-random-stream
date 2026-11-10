import RobustMatching.R7AlgebraInterpretationMain
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Arbitrary original integer weights and the nonnegative-real extension of
the actual marked-pair submodularity theorem, by floor approximation.
-/
noncomputable section
open scoped BigOperators Topology
open Filter Finset

namespace RobustMatching.R7AlgebraInterpretation
open RobustMatching.R2Cut RobustMatching.R7AlgebraPath
open RobustMatching.R7GraphInterpretation
open RobustMatching.R6FableAlgebraSubmodular
variable {V : Type*} [Fintype V] [LinearOrder V]

def sym2NatWeight (w : Edge V → ℕ) (e : Sym2 V) : ℕ :=
  if h : e.toFinset.card = 2 then w ⟨e.toFinset,h⟩ else 0

theorem originalWeight_sym2NatWeight (w : Edge V → ℕ) :
    originalWeight (sym2NatWeight w) = fun e => (w e : ℝ) := by
  funext e
  unfold originalWeight sym2NatWeight
  rw [edgeSym2_toFinset]
  simp [e.property]

/-- Unconditional graph submodularity for arbitrary integer weights on
the project's actual original-edge type. -/
theorem pathValue_submodular_edge_nat (G : Graph V) (w : Edge V → ℕ) :
    Submodular (pathValue (fun e => (w e : ℝ)) G) := by
  have hh := pathValue_submodular_nat G (sym2NatWeight w)
  rwa [originalWeight_sym2NatWeight] at hh

theorem pairWeight_scale (w : Edge V → ℝ) (c : ℝ) (p : Graph V × Graph V) :
    pairWeight (fun e => c*w e) p = c*pairWeight w p := by
  unfold pairWeight
  rw [mul_add,Finset.mul_sum,Finset.mul_sum]

theorem pathValue_scale (w : Edge V → ℝ) (G : Graph V) (M : Finset V)
    (c : ℝ) (hc : 0 ≤ c) :
    pathValue (fun e => c*w e) G M = c*pathValue w G M := by
  apply le_antisymm
  · obtain ⟨p,hp,hval⟩ := pathValue_attained (fun e => c*w e) G M
    obtain ⟨h₁,h₂,hadm⟩ := (mem_feasiblePairs G M p).mp hp
    have hh := mul_le_mul_of_nonneg_left (pairWeight_le_pathValue w h₁ h₂ hadm) hc
    rw [hval,pairWeight_scale]
    exact hh
  · obtain ⟨p,hp,hval⟩ := pathValue_attained w G M
    obtain ⟨h₁,h₂,hadm⟩ := (mem_feasiblePairs G M p).mp hp
    have hh := pairWeight_le_pathValue (fun e => c*w e) h₁ h₂ hadm
    rwa [pairWeight_scale,←hval] at hh

theorem pathValue_submodular_scale (w : Edge V → ℝ) (G : Graph V)
    (hsub : Submodular (pathValue w G)) (c : ℝ) (hc : 0 ≤ c) :
    Submodular (pathValue (fun e => c*w e) G) := by
  intro S T
  simp only [pathValue_scale w G _ c hc]
  have hh := mul_le_mul_of_nonneg_left (hsub S T) hc
  simpa only [mul_add] using hh

/-- Full graph-defined submodularity for nonnegative real weights. The
integer approximation is floor(r*w)/r and all limits concern actual optima. -/
theorem pathValue_submodular_real (G : Graph V) (w : Edge V → ℝ)
    (hw : ∀ e, 0 ≤ w e) : Submodular (pathValue w G) := by
  classical
  let approx : ℝ → Edge V → ℝ := fun r e => (Nat.floor (w e*r) : ℝ) / r
  have hlim : Tendsto approx atTop (𝓝 w) := by
    apply tendsto_pi_nhds.mpr
    intro e
    exact tendsto_nat_floor_mul_div_atTop (hw e)
  have hvalue (M : Finset V) :
      Tendsto (fun r => pathValue (approx r) G M) atTop (𝓝 (pathValue w G M)) :=
    ((continuous_pathValue G M).tendsto w).comp hlim
  intro S T
  apply le_of_tendsto_of_tendsto ((hvalue (S ∪ T)).add (hvalue (S ∩ T)))
    ((hvalue S).add (hvalue T))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  have hh := pathValue_submodular_scale (fun e => (Nat.floor (w e*r) : ℝ)) G
    (pathValue_submodular_edge_nat G (fun e => Nat.floor (w e*r))) r⁻¹ (inv_nonneg.mpr hr)
  simpa only [approx,div_eq_mul_inv,mul_comm] using hh S T

/-- Sharp actual disjoint-demand deletion theorem, with no algebraic or
submodularity hypothesis. Demand sets may have arbitrary finite size. -/
theorem sharp_disjoint_demand_deletion {ι : Type*} [DecidableEq ι]
    (G : Graph V) (w : Edge V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (S : Finset ι) (X : ι → Finset V)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (X i) (X j))
    (N₁ N₂ : Graph V) (h₁ : N₁ ⊆ G) (h₂ : N₂ ⊆ G)
    (hadm : Admissible N₁ N₂ (S.biUnion X)) :
    (∑ i ∈ S, (RobustMatching.R6FableImportance.opt w G -
      RobustMatching.R6FableImportance.opt w (deleteVertices G (X i)))) ≤
      2*RobustMatching.R6FableImportance.opt w G - pairWeight w (N₁,N₂) := by
  have hh := sharp_deletion_bound (pathValue w G) (pathValue_submodular_real G w hw)
    (RobustMatching.R6FableImportance.opt w G) (pathValue_empty w G) S X
    (fun i => RobustMatching.R6FableImportance.opt w (deleteVertices G (X i))) hd
    (fun i _ => pathValue_one_set_upper w G (X i))
    (∑ e ∈ N₁, w e) (∑ e ∈ N₂, w e)
    (pairWeight_le_pathValue w h₁ h₂ hadm)
  unfold pairWeight
  linarith

end RobustMatching.R7AlgebraInterpretation

#print axioms RobustMatching.R7AlgebraInterpretation.pathValue_submodular_edge_nat
#print axioms RobustMatching.R7AlgebraInterpretation.pathValue_submodular_real
#print axioms RobustMatching.R7AlgebraInterpretation.sharp_disjoint_demand_deletion
