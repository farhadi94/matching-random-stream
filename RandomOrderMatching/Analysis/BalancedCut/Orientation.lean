import RandomOrderMatching.Analysis.Profile.MatchingCoordinates
import RandomOrderMatching.Analysis.BalancedCut.DegreeInterface
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Original-consistent orientations built from an actual benchmark
matching. Each matched pair gets one fair coin; each unmatched original
gets one separate fair coin. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RandomOrderMatching.Analysis.BalancedCut
open RandomOrderMatching.Graph RandomOrderMatching.Analysis.Profile

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Block (M : Graph V) := M ⊕ {v : V // v ∉ covered M}

def coordinateCode (M : Graph V) : MatchingVertex M → Block M × Bool
  | .inl (e,i) => (.inl e,decide (i=1))
  | .inr v => (.inr v,false)

theorem coordinateCode_injective (M : Graph V) :
    Function.Injective (coordinateCode M) := by
  intro x y h
  cases x with
  | inl x =>
    rcases x with ⟨e,i⟩
    cases y with
    | inl y =>
      rcases y with ⟨f,j⟩
      have he : e=f := by simpa [coordinateCode] using congrArg Prod.fst h
      subst f
      have hi : i=j := by
        have hh := congrArg Prod.snd h
        fin_cases i <;> fin_cases j <;> simp_all [coordinateCode]
      subst j
      rfl
    | inr v => exact (by simpa [coordinateCode] using congrArg Prod.fst h)
  | inr v =>
    cases y with
    | inl y => exact (by simpa [coordinateCode] using congrArg Prod.fst h)
    | inr u =>
      have hv : v=u := by simpa [coordinateCode] using congrArg Prod.fst h
      subst u
      rfl

def vertexCode (M : Graph V) (hM : Matching M) (v : V) : Block M × Bool :=
  coordinateCode M ((matchingCoordinateEquiv M hM).symm v)

theorem vertexCode_injective (M : Graph V) (hM : Matching M) :
    Function.Injective (vertexCode M hM) :=
  (coordinateCode_injective M).comp (matchingCoordinateEquiv M hM).symm.injective

def block (M : Graph V) (hM : Matching M) (v : V) : Block M := (vertexCode M hM v).1
def parity (M : Graph V) (hM : Matching M) (v : V) : Bool := (vertexCode M hM v).2

theorem block_parity_injective (M : Graph V) (hM : Matching M) {u v : V}
    (hb : block M hM u=block M hM v) (hp : parity M hM u=parity M hM v) : u=v :=
  vertexCode_injective M hM (Prod.ext hb hp)

def side (M : Graph V) (hM : Matching M) (ω : Block M → Bool) (v : V) : Bool :=
  Bool.xor (ω (block M hM v)) (parity M hM v)

theorem same_block_opposite (M : Graph V) (hM : Matching M) {u v : V}
    (hb : block M hM u=block M hM v) (hne : u≠v) (ω : Block M → Bool) :
    side M hM ω u ≠ side M hM ω v := by
  have hp : parity M hM u ≠ parity M hM v := fun h => hne (block_parity_injective M hM hb h)
  unfold side
  rw [hb]
  cases hc : ω (block M hM v) <;> cases hu : parity M hM u <;>
    cases hv : parity M hM v <;> simp_all

theorem vertexCode_endpoint (M : Graph V) (hM : Matching M) (e : M) (i : Fin 2) :
    vertexCode M hM (endpoint e.val i) = (.inl e,decide (i=1)) := by
  change coordinateCode M ((matchingCoordinateEquiv M hM).symm
    ((matchingCoordinateEquiv M hM) (.inl (e,i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Every actual benchmark edge crosses every orientation outcome. -/
theorem benchmark_crosses (M : Graph V) (hM : Matching M) (ω : Block M → Bool)
    (e : Edge V) (he : e∈M) (u v : V) (hu : u∈e.val) (hv : v∈e.val) (hne : u≠v) :
    side M hM ω u ≠ side M hM ω v := by
  obtain ⟨i,rfl⟩ := endpoint_surjective e u hu
  obtain ⟨j,rfl⟩ := endpoint_surjective e v hv
  apply same_block_opposite M hM _ hne ω
  change (vertexCode M hM (endpoint e i)).1 = (vertexCode M hM (endpoint e j)).1
  rw [vertexCode_endpoint M hM ⟨e,he⟩ i,vertexCode_endpoint M hM ⟨e,he⟩ j]

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

def coinPMF : PMF Bool := PMF.ofFintype (fun _ => ((1/2 : ℝ≥0) : ℝ≥0∞)) (by
  have h : ∑ _ : Bool, (1/2 : ℝ≥0) = 1 := by norm_num
  exact_mod_cast h)
def coinMeasure : Measure Bool := coinPMF.toMeasure
instance : IsProbabilityMeasure coinMeasure :=
  inferInstanceAs (IsProbabilityMeasure coinPMF.toMeasure)

theorem integral_coin (f : Bool → ℝ) :
    ∫ z, f z ∂coinMeasure = (f false+f true)/2 := by
  rw [coinMeasure,PMF.integral_eq_sum]
  simp [coinPMF]
  ring

def experiment (M : Graph V) : Measure (Block M → Bool) :=
  Measure.pi (fun _ => coinMeasure)

instance (M : Graph V) : IsProbabilityMeasure (experiment M) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Block M => coinMeasure)))

end RandomOrderMatching.Analysis.BalancedCut
