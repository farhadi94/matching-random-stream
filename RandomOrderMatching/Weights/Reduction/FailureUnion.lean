import RandomOrderMatching.Weights.Reduction.Retirement

/-! Fixed-window success events remain valid for adaptive retirement.
These are exact finite event counts, with no independence premise. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Weights.Reduction.FailureUnion

variable {E I Ω : Type*} [DecidableEq E] [DecidableEq I] [DecidableEq Ω]

def usedWindows (G : Finset E) (windows : E → Finset I) : Finset I :=
  G.biUnion windows

theorem usedWindows_count (G : Finset E) (windows : E → Finset I) (k : ℕ)
    (hcount : ∀ e ∈ G,(windows e).card ≤ k) :
    (usedWindows G windows).card ≤ k*G.card := by
  calc
    _ ≤ ∑ e ∈ G,(windows e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ G,k := Finset.sum_le_sum hcount
    _ = _ := by simp [mul_comm]

def selectedFailure (sample : Finset Ω) (selected : Ω → Finset I)
    (bad : I → Finset Ω) : Finset Ω := by
  classical
  exact sample.filter (fun x => ∃ i ∈ selected x,x ∈ bad i)

/-- Selection may depend on the whole realized stream. Only containment in
the fixed family is needed; no conditional local guarantee is invoked. -/
theorem selectedFailure_count (sample : Finset Ω) (T : Finset I)
    (selected : Ω → Finset I) (bad : I → Finset Ω)
    (hselected : ∀ x ∈ sample, selected x ⊆ T) :
    (selectedFailure sample selected bad).card ≤ ∑ i ∈ T,(bad i).card := by
  classical
  apply (Finset.card_le_card (t := T.biUnion bad) ?_).trans Finset.card_biUnion_le
  intro x hx
  obtain ⟨hxsample,i,hi,hbad⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_biUnion.mpr ⟨i,hselected x hxsample hi,hbad⟩

theorem selectedFailure_fraction (sample : Finset Ω) (T : Finset I)
    (selected : Ω → Finset I) (bad : I → Finset Ω)
    (hselected : ∀ x ∈ sample,selected x ⊆ T) {eta : ℝ}
    (hlocal : ∀ i ∈ T,((bad i).card:ℝ) ≤ eta*(sample.card:ℝ)) :
    ((selectedFailure sample selected bad).card:ℝ) ≤
      (T.card:ℝ)*eta*(sample.card:ℝ) := by
  have hc : ((selectedFailure sample selected bad).card:ℝ) ≤
      ∑ i ∈ T,((bad i).card:ℝ) := by
    exact_mod_cast selectedFailure_count sample T selected bad hselected
  have hs := Finset.sum_le_sum hlocal
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  nlinarith

end RandomOrderMatching.Weights.Reduction.FailureUnion

#print axioms RandomOrderMatching.Weights.Reduction.FailureUnion.usedWindows_count
#print axioms RandomOrderMatching.Weights.Reduction.FailureUnion.selectedFailure_fraction
