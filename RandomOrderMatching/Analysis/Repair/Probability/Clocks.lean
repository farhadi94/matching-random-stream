import RandomOrderMatching.Probability.Batches.Concentration
import RandomOrderMatching.Analysis.Repair.Typed.Availability
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Finite, shared original-label clocks for the final typed repair.
A coordinate has three categories, with probabilities alpha, omega-alpha,
and 1-omega. All copies assigned the same parent read the same coordinate. -/
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace RandomOrderMatching.Analysis.Repair.Probability
open RandomOrderMatching.Analysis.Repair.Typed

abbrev Clock := Fin 3

def alpha : ℝ := 11 / 20
def omega : ℝ := 550001 / 1000000

def mass : Clock → ℝ≥0 := ![11/20, 1/1000000, 449999/1000000]

lemma mass_sum : ∑ z, (mass z : ℝ≥0∞) = 1 := by
  have h : ∑ z, mass z = 1 := by norm_num [mass, Fin.sum_univ_succ]
  exact_mod_cast h

def clockPMF : PMF Clock := PMF.ofFintype (fun z => (mass z : ℝ≥0∞)) mass_sum

def clockMeasure : Measure Clock := clockPMF.toMeasure

instance : IsProbabilityMeasure clockMeasure := inferInstanceAs (IsProbabilityMeasure clockPMF.toMeasure)

def activeBit (z : Clock) : Bool := decide (z = 0)
def earlyBit (z : Clock) : Bool := decide (z ≠ 2)

theorem integral_clock (f : Clock → ℝ) :
    ∫ z, f z ∂clockMeasure = (11/20)*f 0 + (1/1000000)*f 1 + (449999/1000000)*f 2 := by
  rw [clockMeasure, PMF.integral_eq_sum]
  simp [clockPMF, mass, Fin.sum_univ_succ, ENNReal.coe_toReal, NNReal.coe_div]
  ring

@[simp] theorem integral_active : ∫ z, bitMass (activeBit z) ∂clockMeasure = alpha := by
  rw [integral_clock]
  norm_num [activeBit, bitMass, alpha, Fin.ext_iff]

@[simp] theorem integral_inactive : ∫ z, bitMass (!(activeBit z)) ∂clockMeasure = 1-alpha := by
  rw [integral_clock]
  norm_num [activeBit, bitMass, alpha, Fin.ext_iff]

@[simp] theorem integral_early : ∫ z, bitMass (earlyBit z) ∂clockMeasure = omega := by
  rw [integral_clock]
  norm_num [earlyBit, bitMass, omega, Fin.ext_iff]

@[simp] theorem integral_late : ∫ z, bitMass (!(earlyBit z)) ∂clockMeasure = 1-omega := by
  rw [integral_clock]
  norm_num [earlyBit, bitMass, omega, Fin.ext_iff]

variable {B G M J R : Type*}

/-- Parent labels, rather than individual copies, index independent clocks. -/
structure Parents (B G M J R : Type*) where
  gate : G → B
  missing : M → B
  internalMissing : J → B
  root : R → B

def states (p : Parents B G M J R) (z : B → Clock) : States G M J R where
  active := fun g => activeBit (z (p.gate g))
  earlyM := fun m => earlyBit (z (p.missing m))
  earlyJ := fun j => earlyBit (z (p.internalMissing j))
  earlyR := fun r => earlyBit (z (p.root r))

def experiment [Fintype B] : Measure (B → Clock) := Measure.pi (fun _ => clockMeasure)

instance [Fintype B] : IsProbabilityMeasure (experiment (B := B)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : B => clockMeasure)))

lemma bitMass_bounds (b : Bool) : bitMass b ∈ Set.Icc (0:ℝ) 1 := by
  cases b <;> norm_num [bitMass]

lemma integral_clock_mono {f g : Clock → ℝ} (h : ∀ z, f z ≤ g z) :
    ∫ z, f z ∂clockMeasure ≤ ∫ z, g z ∂clockMeasure := by
  rw [integral_clock, integral_clock]
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  linarith

end RandomOrderMatching.Analysis.Repair.Probability
