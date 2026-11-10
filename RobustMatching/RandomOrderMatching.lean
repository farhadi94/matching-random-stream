import RobustMatching.R8StreamingWrapperArbitrary
import RobustMatching.R8StreamingWrapperUniform

/-!
# Random-order matching

Public entry points for the actual streaming algorithms and their approximation
guarantees. Every finite graph is represented by unordered two-element edges;
no bipartiteness assumption is needed, so the results include both general and
bipartite graphs. The bounded-integer algorithm returns a 0.71295 approximation
with the requested failure probability. The window compiler gives
0.71295 - epsilon for positive rational weights, independently of their range.

`arbitrary_weight_stream_output_eq` exposes the actual retained-window state
and EOF decoder, rather than leaving the streaming implementation implicit in
the list-based probability statement. Storage theorems are in the separate
R8StreamingResources modules. Extracted matching-oracle running time and
machine serialization are outside this mathematical correctness interface.
-/
noncomputable section
open Classical
open scoped BigOperators
namespace RobustMatching.RandomOrderMatching
open RobustMatching.R2Cut RobustMatching.R8WeightWindows
open RobustMatching.R7ProbabilityRestriction
variable {V : Type*} [Fintype V] [LinearOrder V]

abbrev approximationRatio : ℝ := R8StreamingWrapper.finalRatio

abbrev boundedIntegerAlgorithm (W : ℕ) (delta : ℝ) (hW : 0 < W) : Machine V :=
  R8StreamingWrapper.confidentMachine W delta hW

abbrev arbitraryWeightAlgorithm (epsilon delta : ℝ) (he : 0 < epsilon)
    (w : Edge V → ℚ) (l : List (Edge V)) : Graph V :=
  R8StreamingWrapper.arbitraryOutput epsilon delta he w l

abbrev arbitraryWeightStreamAlgorithm (epsilon delta : ℝ) (he : 0 < epsilon)
    (w : Edge V → ℚ) (stream : ℕ → Edge V) (t : ℕ) : Graph V :=
  R8StreamingWrapper.arbitraryStreamOutput epsilon delta he w stream t

theorem bounded_integer_contract (W : ℕ) (hW : 0 < W)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1) :
    (boundedIntegerAlgorithm (V:=V) W delta hW).Contract W approximationRatio delta :=
  R8StreamingWrapper.confidentMachine_contract W hW delta hd hd1

theorem bounded_integer_approximation (W : ℕ) (hW : 0 < W)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (w : Edge V → ℕ) (l : List (Edge V)) (hnd : l.Nodup)
    (hw : ∀ e ∈ l,1 ≤ w e ∧ w e ≤ W) :
    permMean l (fun u => if
      (boundedIntegerAlgorithm (V:=V) W delta hW).Good approximationRatio w u then 0 else 1) ≤ delta :=
  R8StreamingWrapper.bounded_integer_random_order W hW delta hd hd1 w l hnd hw

theorem unweighted_approximation (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (l : List (Edge V)) (hnd : l.Nodup) :
    permMean l (fun u => if
      (boundedIntegerAlgorithm (V:=V) 1 delta (by decide)).Good approximationRatio (fun _ => 1) u
      then 0 else 1) ≤ delta :=
  R8StreamingWrapper.unweighted_random_order delta hd hd1 l hnd

/-- Direct EOF output for a globally bounded integer weight function. -/
abbrev boundedIntegerOutput (W : ℕ) (delta : ℝ) (hW : 0 < W)
    (w : Edge V → ℕ) (hw : ∀ e,w e ≤ W) (l : List (Edge V)) : Graph V :=
  let L := R8StreamingWrapper.confidenceLog (Fintype.card V) W delta
  let Q := R8StreamingWrapper.canonicalBudget V W L
  R8StreamingWrapper.finalBoundedOutput w W L
    (R8StreamingWrapper.capLog (Fintype.card V) W Q delta) (R8StreamingWrapper.prefixLog delta)
    hw hW (R8StreamingWrapper.confidenceLog_pos _ _ _) l

theorem bounded_integer_label_permutations {m : ℕ}
    (W : ℕ) (hW : 0 < W) (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (w : Edge V → ℕ) (hw : ∀ e,w e ≤ W)
    (label : Fin m → Edge V) (hi : Function.Injective label)
    (hpos : ∀ e ∈ Finset.univ.image label,1 ≤ w e) :
    ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
      (∑ e ∈ boundedIntegerOutput W delta hW w hw (R8StreamingWrapper.labelledStream label pi),(w e:ℝ)) <
      approximationRatio*R6FableImportance.opt (fun e => (w e:ℝ)) (Finset.univ.image label))).card:ℝ)/
        Fintype.card (Equiv.Perm (Fin m)) ≤ delta :=
  R8StreamingWrapper.finalBoundedOutput_uniform_probability W hW delta hd hd1 w hw label hi hpos

theorem arbitrary_weight_valid (epsilon delta : ℝ) (he : 0 < epsilon)
    (w : Edge V → ℚ) (l : List (Edge V)) :
    Matching (arbitraryWeightAlgorithm epsilon delta he w l) ∧
      arbitraryWeightAlgorithm epsilon delta he w l ⊆ l.toFinset :=
  R8StreamingWrapper.arbitraryOutput_valid epsilon delta he w l

theorem arbitrary_weight_stream_output_eq (epsilon delta : ℝ) (he : 0 < epsilon)
    (w : Edge V → ℚ) (stream : ℕ → Edge V) (t : ℕ) :
    arbitraryWeightStreamAlgorithm epsilon delta he w stream t=
      arbitraryWeightAlgorithm epsilon delta he w (streamList stream t) :=
  R8StreamingWrapper.arbitraryStreamOutput_eq epsilon delta he w stream t

theorem arbitrary_weight_approximation (epsilon delta : ℝ)
    (he : 0 < epsilon) (hd : 0 < delta) (hd1 : delta < 1)
    (w : Edge V → ℚ) (hw : ∀ e,0 < w e)
    (l : List (Edge V)) (hnd : l.Nodup) (M : Graph V) (hM : IsOptimum w l M) :
    permMean l (fun u => if (approximationRatio-epsilon)*(∑ e ∈ M,(w e:ℝ)) ≤
      ∑ e ∈ arbitraryWeightAlgorithm epsilon delta he w u,(w e:ℝ) then 0 else 1) ≤ delta :=
  R8StreamingWrapper.arbitrary_weight_random_order epsilon delta he hd hd1 w hw l hnd M hM

end RobustMatching.RandomOrderMatching
