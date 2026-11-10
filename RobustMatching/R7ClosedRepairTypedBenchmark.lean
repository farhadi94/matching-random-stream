import RobustMatching.R7ClosedRepairTypedModel

/-! The selected copied benchmark is an actual matching, with exact
typed counts and the internal U/N pair credits. The canonical finite
sum types are an explicit labeling of the cover/benchmark partition. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RobustMatching.R7ClosedRepair.Typed
open RobustMatching.R7ClosedRepair

abbrev Benchmarks (R G M I J : Type*) := R ⊕ G ⊕ M ⊕ I ⊕ J

variable {G M P I J R U : Type*}

def endpoint (b : Benchmarks R G M I J) (t : Bool) :
    Centers G M P I J ⊕ Outsides R M G U :=
  match b with
  | .inl r => .inr (.inl (r,t))
  | .inr (.inl g) =>
      if t then .inr (.inr (.inr (.inl g))) else .inl (.inl g)
  | .inr (.inr (.inl m)) =>
      if t then .inr (.inr (.inl m)) else .inl (.inr (.inl m))
  | .inr (.inr (.inr (.inl i))) => .inl (.inr (.inr (.inr (.inl (i,t)))))
  | .inr (.inr (.inr (.inr j))) => .inl (.inr (.inr (.inr (.inr (j,t)))))

theorem endpoint_injective : Function.Injective
    (fun z : Benchmarks R G M I J × Bool => endpoint (P := P) (U := U) z.1 z.2) := by
  intro z z' h
  rcases z with ⟨b,t⟩
  rcases z' with ⟨b',t'⟩
  rcases b with r | g | m | i | j <;>
    rcases b' with r' | g' | m' | i' | j' <;>
    cases t <;> cases t' <;> simp_all [endpoint]

lemma endpoint_ne (b : Benchmarks R G M I J) :
    endpoint (P := P) (U := U) b false ≠ endpoint (P := P) (U := U) b true := by
  intro h
  have hh := endpoint_injective (P := P) (U := U) (a₁ := (b,false)) (a₂ := (b,true)) h
  have := congrArg Prod.snd hh
  simp at this

def benchmarkEdge (b : Benchmarks R G M I J) :
    R2Cut.Edge (Centers G M P I J ⊕ Outsides R M G U) :=
  ⟨{endpoint b false, endpoint b true}, by simp [endpoint_ne b]⟩

theorem benchmarkEdge_injective : Function.Injective
    (benchmarkEdge (P := P) (U := U) : Benchmarks R G M I J → _) := by
  intro b b' h
  have hm : endpoint (P := P) (U := U) b false ∈ (benchmarkEdge (P := P) (U := U) b').val := by
    rw [← h]
    simp [benchmarkEdge]
  rcases (by simpa [benchmarkEdge] using hm) with h0 | h1
  · exact congrArg Prod.fst (endpoint_injective (P := P) (U := U) (a₁ := (b,false)) (a₂ := (b',false)) h0)
  · exact congrArg Prod.fst (endpoint_injective (P := P) (U := U) (a₁ := (b,false)) (a₂ := (b',true)) h1)

variable [Fintype G] [Fintype M] [Fintype P] [Fintype I]
  [Fintype J] [Fintype R] [Fintype U]

def selectedBench (s : States G M J R) : Benchmarks R G M I J → Prop
  | .inl r => s.earlyR r = false
  | .inr (.inl g) => s.active g = false
  | .inr (.inr (.inl m)) => s.earlyM m = false
  | .inr (.inr (.inr (.inl _))) => True
  | .inr (.inr (.inr (.inr j))) => s.earlyJ j = false

def selectedWeight (s : States G M J R) : Benchmarks R G M I J → ℝ
  | .inl r => if s.earlyR r = false then 1 else 0
  | .inr (.inl g) => if s.active g = false then 1 else 0
  | .inr (.inr (.inl m)) => if s.earlyM m = false then 1 else 0
  | .inr (.inr (.inr (.inl _))) => 1
  | .inr (.inr (.inr (.inr j))) => if s.earlyJ j = false then 1 else 0

lemma selected_indicator (s : States G M J R) (b : Benchmarks R G M I J) :
    (if selectedBench s b then (1 : ℝ) else 0) = selectedWeight s b := by
  rcases b with r | g | m | i | j
  · exact (ite_eq_ite _ _ _).mpr trivial
  · exact (ite_eq_ite _ _ _).mpr trivial
  · exact (ite_eq_ite _ _ _).mpr trivial
  · exact if_pos trivial
  · exact (ite_eq_ite _ _ _).mpr trivial

def selectedEdges (s : States G M J R) :
    R2Cut.Graph (Centers G M P I J ⊕ Outsides R M G U) :=
  ((Finset.univ : Finset (Benchmarks R G M I J)).filter (selectedBench s)).image benchmarkEdge

theorem selectedEdges_matching (s : States G M J R) :
    R2Cut.Matching (selectedEdges (P := P) (I := I) (U := U) s) := by
  intro e he f hf hne
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hf
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  have hbb : b ≠ b' := fun h => hne (congrArg benchmarkEdge h)
  simp only [benchmarkEdge, Finset.mem_insert, Finset.mem_singleton] at hv hv'
  rcases hv with rfl | rfl <;> rcases hv' with hh | hh
  · exact hbb (congrArg Prod.fst (endpoint_injective (P := P) (U := U) (a₁ := (b,false)) (a₂ := (b',false)) hh))
  · exact hbb (congrArg Prod.fst (endpoint_injective (P := P) (U := U) (a₁ := (b,false)) (a₂ := (b',true)) hh))
  · exact hbb (congrArg Prod.fst (endpoint_injective (P := P) (U := U) (a₁ := (b,true)) (a₂ := (b',false)) hh))
  · exact hbb (congrArg Prod.fst (endpoint_injective (P := P) (U := U) (a₁ := (b,true)) (a₂ := (b',true)) hh))

lemma selectedEdges_card (s : States G M J R) :
    ((selectedEdges (P := P) (I := I) (U := U) s).card : ℝ) =
      ∑ b : Benchmarks R G M I J, if selectedBench s b then (1 : ℝ) else 0 := by
  rw [selectedEdges, Finset.card_image_of_injective _ benchmarkEdge_injective]
  simp

/-- Exact mass of the selected matching: each internal U pair contributes
one, and each internal N pair contributes precisely its late indicator. -/
theorem selectedEdges_typed_count (s : States G M J R) :
    ((selectedEdges (P := P) (I := I) (U := U) s).card : ℝ) =
      (∑ r, if s.earlyR r = false then (1 : ℝ) else 0) +
      (∑ g, if s.active g = false then (1 : ℝ) else 0) +
      (∑ m, if s.earlyM m = false then (1 : ℝ) else 0) +
      (Fintype.card I : ℝ) +
      (∑ j, if s.earlyJ j = false then (1 : ℝ) else 0) := by
  rw [selectedEdges_card]
  simp_rw [selected_indicator]
  simp only [Fintype.sum_sum_type, selectedWeight,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

theorem active_inactive_count (s : States G M J R) :
    (∑ g, if s.active g = true then (1 : ℝ) else 0) +
      (∑ g, if s.active g = false then (1 : ℝ) else 0) = Fintype.card G := by
  rw [← Finset.sum_add_distrib]
  calc
    (∑ g, ((if s.active g = true then (1 : ℝ) else 0) +
      (if s.active g = false then 1 else 0))) = ∑ _g : G, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro g _
        cases s.active g <;> simp
    _ = Fintype.card G := by simp

theorem exact_bare_credit (s : States G M J R) :
    2 * (∑ g, if s.active g = true then (1 : ℝ) else 0) +
      ((selectedEdges (P := P) (I := I) (U := U) s).card : ℝ) =
      (Fintype.card G : ℝ) +
      (∑ g, if s.active g = true then (1 : ℝ) else 0) +
      (∑ r, if s.earlyR r = false then (1 : ℝ) else 0) +
      (∑ m, if s.earlyM m = false then (1 : ℝ) else 0) +
      (Fintype.card I : ℝ) +
      (∑ j, if s.earlyJ j = false then (1 : ℝ) else 0) := by
  rw [selectedEdges_typed_count]
  have h := active_inactive_count s
  linarith

theorem center_count :
    Fintype.card (Centers G M P I J) = Fintype.card G + Fintype.card M +
      Fintype.card P + 2 * Fintype.card I + 2 * Fintype.card J := by
  simp [Centers, Fintype.card_sum, Fintype.card_prod]
  omega

theorem benchmark_count :
    Fintype.card (Benchmarks R G M I J) = Fintype.card R + Fintype.card G +
      Fintype.card M + Fintype.card I + Fintype.card J := by
  simp [Benchmarks, Fintype.card_sum]
  omega

end RobustMatching.R7ClosedRepair.Typed
