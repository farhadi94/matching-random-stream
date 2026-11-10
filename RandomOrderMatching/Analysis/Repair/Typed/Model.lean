import RandomOrderMatching.Analysis.Repair.Typed.MatchingConstruction

/-! A concrete typed cover model. Every available/missing gate has one
center and its own outside partner. Internal benchmark pairs have two
distinct center copies. The selected endpoints and active-gate occupancy
are computed from actual per-edge Boolean states, not supplied as load
or profile assumptions. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical

namespace RandomOrderMatching.Analysis.Repair.Typed
open RandomOrderMatching.Analysis.Repair

abbrev Centers (G M P I J : Type*) := G ⊕ M ⊕ P ⊕ (I × Bool) ⊕ (J × Bool)
abbrev Outsides (R M G U : Type*) := (R × Bool) ⊕ M ⊕ G ⊕ U

structure States (G M J R : Type*) where
  active : G → Bool
  earlyM : M → Bool
  earlyJ : J → Bool
  earlyR : R → Bool

variable {G M P I J R U : Type*}
variable (s : States G M J R)

def centerSelected : Centers G M P I J → Prop
  | .inl g => s.active g = false
  | .inr (.inl m) => s.earlyM m = false
  | .inr (.inr (.inl _)) => False
  | .inr (.inr (.inr (.inl _))) => True
  | .inr (.inr (.inr (.inr j))) => s.earlyJ j.1 = false

def outsideSelected : Outsides R M G U → Prop
  | .inl r => s.earlyR r.1 = false
  | .inr (.inl m) => s.earlyM m = false
  | .inr (.inr (.inl g)) => s.active g = false
  | .inr (.inr (.inr _)) => False

def centerOccupied : Centers G M P I J → Prop
  | .inl g => s.active g = true
  | _ => False

def outsideOccupied : Outsides R M G U → Prop
  | .inr (.inr (.inl g)) => s.active g = true
  | _ => False

def centerSurvives (side : Centers G M P I J → Bool)
    (layer : Bool) (c : Centers G M P I J) : Prop :=
  ¬(centerSelected s c ∧ side c = layer)

def outsideSurvives (side : Outsides R M G U → Bool)
    (layer : Bool) (x : Outsides R M G U) : Prop :=
  ¬(outsideSelected s x ∧ side x = layer)

def gateRelation : Centers G M P I J → Outsides R M G U → Prop
  | .inl g, .inr (.inr (.inl g')) => g = g' ∧ s.active g = true
  | _, _ => False

def gateMatrix (c : Centers G M P I J) (x : Outsides R M G U) : ℝ :=
  if gateRelation s c x then 1 else 0

lemma gate_occupied {c : Centers G M P I J} {x : Outsides R M G U}
    (h : gateRelation s c x) : centerOccupied s c ∧ outsideOccupied s x := by
  rcases c with g | m | p | i | j <;>
    rcases x with r | m' | g' | u <;>
    simp_all [gateRelation, centerOccupied, outsideOccupied]
  aesop

lemma occupied_center_not_selected {c : Centers G M P I J}
    (h : centerOccupied s c) : ¬centerSelected s c := by
  rcases c with g | m | p | i | j <;>
    simp_all [centerOccupied, centerSelected]

lemma occupied_outside_not_selected {x : Outsides R M G U}
    (h : outsideOccupied s x) : ¬outsideSelected s x := by
  rcases x with r | m | g | u <;>
    simp_all [outsideOccupied, outsideSelected]

lemma gate_survives (sideC : Centers G M P I J → Bool)
    (sideO : Outsides R M G U → Bool) (layer : Bool)
    {c : Centers G M P I J} {x : Outsides R M G U}
    (h : gateRelation s c x) :
    centerSurvives s sideC layer c ∧ outsideSurvives s sideO layer x := by
  obtain ⟨hc, hx⟩ := gate_occupied s h
  exact ⟨fun h => occupied_center_not_selected s hc h.1,
    fun h => occupied_outside_not_selected s hx h.1⟩

def deletionAdj (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (layer : Bool) (c : Centers G M P I J) (x : Outsides R M G U) : Prop :=
  (H c x ∨ gateRelation s c x) ∧
    centerSurvives s sideC layer c ∧ outsideSurvives s sideO layer x

def rawSupport (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (scale : Bool → Outsides R M G U → ℝ)
    (layer : Bool) (c : Centers G M P I J) (x : Outsides R M G U) : ℝ :=
  if H c x ∧ centerSurvives s sideC layer c ∧ outsideSurvives s sideO layer x ∧
      ¬centerOccupied s c ∧ ¬outsideOccupied s x
    then w c x / scale layer x else 0

variable [Fintype G] [Fintype M] [Fintype P] [Fintype I]
  [Fintype J] [Fintype R] [Fintype U]

lemma gate_row (c : Centers G M P I J) :
    rowLoad (gateMatrix (P := P) (I := I) (U := U) s) c =
      if centerOccupied s c then 1 else 0 := by
  rcases c with g | m | p | i | j <;>
    simp +instances [rowLoad, gateMatrix, gateRelation, centerOccupied,
      Fintype.sum_sum_type]
  by_cases h : s.active g = true <;> simp [h]

lemma gate_col (x : Outsides R M G U) :
    colLoad (gateMatrix (P := P) (I := I) (U := U) s) x =
      if outsideOccupied s x then 1 else 0 := by
  rcases x with r | m | g | u <;>
    simp +instances [colLoad, gateMatrix, gateRelation, outsideOccupied,
      Fintype.sum_sum_type]
  rw [Finset.sum_eq_single g]
  · simp
    exact (ite_eq_ite _ _ _).mpr trivial
  · intro b _ hb
    simp [hb]
  · simp

def centerGateMass : Centers G M P I J → ℝ
  | .inl g => if s.active g = true then 1 else 0
  | _ => 0

lemma gate_row_explicit (c : Centers G M P I J) :
    rowLoad (gateMatrix (P := P) (I := I) (U := U) s) c = centerGateMass s c := by
  rw [gate_row]
  rcases c with g | m | p | i | j
  · exact (ite_eq_ite _ _ _).mpr trivial
  all_goals exact if_neg (by simp [centerOccupied])

lemma gate_mass : mass (gateMatrix (P := P) (I := I) (U := U) s :
    Centers G M P I J → Outsides R M G U → ℝ) =
    ∑ g, if s.active g = true then (1 : ℝ) else 0 := by
  change (∑ c, rowLoad (gateMatrix (P := P) (I := I) (U := U) s) c) = _
  simp_rw [gate_row_explicit]
  simp [centerGateMass, Fintype.sum_sum_type]

lemma raw_nonneg
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (scale : Bool → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (hs : ∀ layer x, 0 < scale layer x)
    (layer : Bool) : ∀ c x, 0 ≤ rawSupport s H sideC sideO w scale layer c x := by
  intro c x
  unfold rawSupport
  split_ifs
  · exact div_nonneg (hw c x) (hs layer x).le
  · rfl

lemma raw_graph_support
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (scale : Bool → Outsides R M G U → ℝ) (layer : Bool) :
    ∀ c x, ¬deletionAdj s H sideC sideO layer c x →
      rawSupport s H sideC sideO w scale layer c x = 0 := by
  intro c x hn
  unfold rawSupport
  split_ifs with hh
  · exact False.elim (hn ⟨Or.inl hh.1, hh.2.1, hh.2.2.1⟩)
  · rfl

lemma gate_graph_support
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (layer : Bool) :
    ∀ c x, ¬deletionAdj s H sideC sideO layer c x → gateMatrix (P := P) (I := I) (U := U) s c x = 0 := by
  intro c x hn
  unfold gateMatrix
  split_ifs with hh
  · obtain ⟨hc, hx⟩ := gate_survives s sideC sideO layer hh
    exact False.elim (hn ⟨Or.inr hh, hc, hx⟩)
  · rfl

lemma raw_occupied_row
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (scale : Bool → Outsides R M G U → ℝ) (layer : Bool)
    {c : Centers G M P I J} (hc : centerOccupied s c) :
    rowLoad (rawSupport s H sideC sideO w scale layer) c = 0 := by
  simp [rowLoad, rawSupport, hc]

lemma raw_occupied_col
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (scale : Bool → Outsides R M G U → ℝ) (layer : Bool)
    {x : Outsides R M G U} (hx : outsideOccupied s x) :
    colLoad (rawSupport s H sideC sideO w scale layer) x = 0 := by
  simp [colLoad, rawSupport, hx]

/-- The actual typed deletion graph has a matching attaining the gate
mass plus clipped outside loads minus center overload. Endpoint survival
and active-gate collision avoidance are proved by the construction. -/
theorem actual_typed_matching
    (H : Centers G M P I J → Outsides R M G U → Prop)
    (sideC : Centers G M P I J → Bool) (sideO : Outsides R M G U → Bool)
    (w : Centers G M P I J → Outsides R M G U → ℝ)
    (scale : Bool → Outsides R M G U → ℝ)
    (hw : ∀ c x, 0 ≤ w c x) (hs : ∀ layer x, 0 < scale layer x)
    (layer : Bool) :
    ∃ T : RandomOrderMatching.Graph.Graph (Centers G M P I J ⊕ Outsides R M G U),
      T ⊆ RandomOrderMatching.Graph.BipartiteMatrix.graphEdges (deletionAdj s H sideC sideO layer) ∧
      RandomOrderMatching.Graph.Matching T ∧
      (∑ g, if s.active g = true then (1 : ℝ) else 0) +
        (∑ x, min (colLoad (rawSupport s H sideC sideO w scale layer) x) 1) -
        (∑ c, max (rowLoad (rawSupport s H sideC sideO w scale layer) c - 1) 0)
          ≤ (T.card : ℝ) := by
  have hg : ∀ c x, 0 ≤ gateMatrix (P := P) (I := I) (U := U) s c x := by
    intro c x
    simp only [gateMatrix]
    split_ifs <;> norm_num
  have hrow : ∀ c, rowLoad (gateMatrix (P := P) (I := I) (U := U) s) c = 0 ∨
      rowLoad (rawSupport s H sideC sideO w scale layer) c = 0 := by
    intro c
    by_cases hc : centerOccupied s c
    · exact Or.inr (raw_occupied_row s H sideC sideO w scale layer hc)
    · exact Or.inl (by simp [gate_row, hc])
  have hcol : ∀ x, colLoad (gateMatrix (P := P) (I := I) (U := U) s) x = 0 ∨
      colLoad (rawSupport s H sideC sideO w scale layer) x = 0 := by
    intro x
    by_cases hx : outsideOccupied s x
    · exact Or.inr (raw_occupied_col s H sideC sideO w scale layer hx)
    · exact Or.inl (by simp [gate_col, hx])
  have hgr : ∀ c, rowLoad (gateMatrix (P := P) (I := I) (U := U) s) c ≤ 1 := by
    intro c
    rw [gate_row]
    split_ifs <;> norm_num
  have hgc : ∀ x, colLoad (gateMatrix (P := P) (I := I) (U := U) s) x ≤ 1 := by
    intro x
    rw [gate_col]
    split_ifs <;> norm_num
  obtain ⟨T, hT, hm, hv⟩ := gated_repair_matching
    (deletionAdj s H sideC sideO layer) (gateMatrix (P := P) (I := I) (U := U) s)
    (rawSupport s H sideC sideO w scale layer) hg
    (raw_nonneg s H sideC sideO w scale hw hs layer)
    (gate_graph_support s H sideC sideO layer)
    (raw_graph_support s H sideC sideO w scale layer) hgr hgc hrow hcol
  rw [gate_mass] at hv
  exact ⟨T, hT, hm, hv⟩

end RandomOrderMatching.Analysis.Repair.Typed
