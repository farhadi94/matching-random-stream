import RobustMatching.R8PermutationClockChronology

/-! Exact original-label reindexing and transfer of repaired-clock events
to an actual uniformly random stream. -/
noncomputable section
set_option maxHeartbeats 800000
open Classical MeasureTheory
namespace RobustMatching.R8PermutationClock
open R8RepairProbability

def labeledClocks {n : ℕ} {B : Type*} (e : Fin n ≃ B)
    (s : (Fin n → Clock) × Equiv.Perm (Fin n)) : B → Clock :=
  fun b => coupledClocks s (e.symm b)

def labeledOrder {n : ℕ} {B : Type*} (e : Fin n ≃ B)
    (s : (Fin n → Clock) × Equiv.Perm (Fin n)) : Fin n ≃ B :=
  (coupledOrder s).trans e

lemma clock_reindex_preserving {n : ℕ} {B : Type*} [Fintype B] (e : Fin n ≃ B) :
    MeasurePreserving (fun z : Fin n → Clock => fun b => z (e.symm b))
      (experiment (B := Fin n)) (experiment (B := B)) := by
  convert measurePreserving_piCongrLeft (fun _ : B => clockMeasure) e using 1
  · funext z b
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']
  · rfl
  · rfl

theorem labeledClocks_preserving {n : ℕ} {B : Type*} [Fintype B] (e : Fin n ≃ B) :
    MeasurePreserving (labeledClocks e) (coupling n) (experiment (B := B)) :=
  (clock_reindex_preserving e).comp (coupledClocks_preserving n)

@[simp] theorem labeledClocks_order {n : ℕ} {B : Type*} (e : Fin n ≃ B)
    (s : (Fin n → Clock) × Equiv.Perm (Fin n)) (i : Fin n) :
    labeledClocks e s (labeledOrder e s i) = coupledClocks s (coupledOrder s i) := by
  simp [labeledClocks, labeledOrder]

theorem labeled_chronology {n : ℕ} {B : Type*} (e : Fin n ≃ B)
    (s : (Fin n → Clock) × Equiv.Perm (Fin n)) :
    Monotone (fun i => labeledClocks e s (labeledOrder e s i)) := by
  simpa only [labeledClocks_order] using coupled_chronology s

theorem labeled_bracket_chronology {n : ℕ} {B : Type*} (e : Fin n ≃ B)
    (s : (Fin n → Clock) × Equiv.Perm (Fin n)) (c : ℕ)
    (hc : cutoffBracket c (coupledClocks s)) :
    (∀ b, labeledClocks e s b = 0 → ((labeledOrder e s).symm b).val < c) ∧
    (∀ b, labeledClocks e s b = 2 → c ≤ ((labeledOrder e s).symm b).val) := by
  obtain ⟨ha,hl⟩ := coupled_bracket_chronology s c hc
  constructor
  · intro b hb
    exact ha (e.symm b) hb
  · intro b hb
    exact hl (e.symm b) hb

lemma preserving_real_preimage {A D : Type*} [MeasurableSpace A] [MeasurableSpace D]
    {μ : Measure A} {ν : Measure D} {f : A → D} (h : MeasurePreserving f μ ν)
    (S : Set D) (hS : MeasurableSet S) : μ.real (f ⁻¹' S) = ν.real S :=
  congrArg ENNReal.toReal (h.measure_preimage hS.nullMeasurableSet)

/-- A pathwise implication on the constructed coupling transfers an actual
clock-event bound to the uniform stream. There is no assumed coupling or
conditional-copy independence premise. -/
theorem uniform_stream_bad_bound {n : ℕ} {B : Type*} [Fintype B]
    (e : Fin n ≃ B) (bad : Set (Equiv.Perm (Fin n))) (good : Set (B → Clock))
    (c : ℕ) {δ t : ℝ} (hn : 0 < n) (ht : 0 < t)
    (hleft : alpha*n+t ≤ c) (hright : (c:ℝ) ≤ omega*n-t)
    (hgood : (experiment (B := B)).real goodᶜ ≤ δ)
    (hpath : ∀ s, labeledClocks e s ∈ good → cutoffBracket c (coupledClocks s) →
      coupledOrder s ∉ bad) :
    (uniformOrder n).real bad ≤ δ + 2 * Real.exp (-2*t^2/n) := by
  have horder := preserving_real_preimage (coupledOrder_preserving n) bad
    (Set.toFinite bad).measurableSet
  rw [← horder]
  have hin : coupledOrder ⁻¹' bad ⊆
      labeledClocks e ⁻¹' goodᶜ ∪ {s | ¬cutoffBracket c (coupledClocks s)} := by
    intro s hs
    by_cases hg : labeledClocks e s ∈ good
    · right
      exact fun hc => hpath s hg hc hs
    · exact Or.inl hg
  refine (measureReal_mono hin).trans ((measureReal_union_le _ _).trans ?_)
  have hclock := preserving_real_preimage (labeledClocks_preserving e) goodᶜ
    (Set.toFinite goodᶜ).measurableSet
  rw [hclock]
  exact add_le_add hgood (coupled_cutoffBracket_failure hn c ht hleft hright)

end RobustMatching.R8PermutationClock
