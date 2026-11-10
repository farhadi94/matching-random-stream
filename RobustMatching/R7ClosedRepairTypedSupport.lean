import RobustMatching.R7ClosedRepairClipping

/-! Actual gated repair matrices and their graph matchings. All capacity
claims below concern the constructed, clipped matrices. The local load
inequalities used later are explicit deterministic events, not an assumed
profile approximation theorem. -/
noncomputable section
open scoped BigOperators
open Classical

namespace RobustMatching.R7ClosedRepair.Typed
open RobustMatching.R7ClosedRepair

variable {C O : Type*} [Fintype C] [Fintype O]

lemma row_overload_identity (f : C → O → ℝ) :
    mass f - (∑ c, min (rowLoad f c) 1) =
      ∑ c, max (rowLoad f c - 1) 0 := by
  change (∑ c, rowLoad f c) - _ = _
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ => sub_min_eq_overload _

lemma col_overload_identity (f : C → O → ℝ) :
    mass f - (∑ x, min (colLoad f x) 1) =
      ∑ x, max (colLoad f x - 1) 0 := by
  rw [mass_cols, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => sub_min_eq_overload _

/-- Equivalent clipping estimate with the useful outside contribution
`min(raw outside load,1)` and only center overload subtracted. -/
theorem repaired_mass_lower_columns (f : C → O → ℝ)
    (hf : ∀ c x, 0 ≤ f c x) :
    (∑ x, min (colLoad f x) 1) -
        (∑ c, max (rowLoad f c - 1) 0) ≤ mass (repaired f) := by
  have h := repaired_mass_lower f hf
  have hr := row_overload_identity f
  have hc := col_overload_identity f
  linarith

def withGates (g f : C → O → ℝ) : C → O → ℝ :=
  fun c x => g c x + repaired f c x

lemma withGates_nonneg (g f : C → O → ℝ)
    (hg : ∀ c x, 0 ≤ g c x) (hf : ∀ c x, 0 ≤ f c x) :
    ∀ c x, 0 ≤ withGates g f c x := by
  intro c x
  exact add_nonneg (hg c x) (repaired_nonneg f hf c x)

lemma withGates_support (adj : C → O → Prop) (g f : C → O → ℝ)
    (hf : ∀ c x, 0 ≤ f c x)
    (hgs : ∀ c x, ¬adj c x → g c x = 0)
    (hfs : ∀ c x, ¬adj c x → f c x = 0) :
    ∀ c x, ¬adj c x → withGates g f c x = 0 := by
  intro c x hn
  simp [withGates, hgs c x hn, repaired_support f hf adj hfs c x hn]

lemma withGates_row (g f : C → O → ℝ)
    (hf : ∀ c x, 0 ≤ f c x)
    (hgr : ∀ c, rowLoad g c ≤ 1)
    (hsep : ∀ c, rowLoad g c = 0 ∨ rowLoad f c = 0) (c : C) :
    rowLoad (withGates g f) c ≤ 1 := by
  have heq : rowLoad (withGates g f) c = rowLoad g c + rowLoad (repaired f) c := by
    simp [rowLoad, withGates, Finset.sum_add_distrib]
  rw [heq]
  rcases hsep c with h | h
  · rw [h, zero_add]
    exact repaired_row_le_one f hf c
  · have hh : rowLoad (repaired f) c ≤ rowLoad f c :=
      Finset.sum_le_sum fun x _ => repaired_le f hf c x
    linarith [hgr c]

lemma withGates_col (g f : C → O → ℝ)
    (hf : ∀ c x, 0 ≤ f c x)
    (hgc : ∀ x, colLoad g x ≤ 1)
    (hsep : ∀ x, colLoad g x = 0 ∨ colLoad f x = 0) (x : O) :
    colLoad (withGates g f) x ≤ 1 := by
  have heq : colLoad (withGates g f) x = colLoad g x + colLoad (repaired f) x := by
    simp [colLoad, withGates, Finset.sum_add_distrib]
  rw [heq]
  rcases hsep x with h | h
  · rw [h, zero_add]
    exact repaired_col_le_one f hf x
  · have hh : colLoad (repaired f) x ≤ colLoad f x :=
      Finset.sum_le_sum fun c _ => repaired_le f hf c x
    linarith [hgc x]

lemma withGates_mass (g f : C → O → ℝ) :
    mass (withGates g f) = mass g + mass (repaired f) := by
  simp [mass, withGates, Finset.sum_add_distrib]

/-- Unit gates may occupy rows and columns, but raw repair support must
avoid those occupied vertices. The conclusion is an actual integral
matching in the declared incidence graph, including the gate value. -/
theorem gated_repair_matching [DecidableEq C] [DecidableEq O]
    (adj : C → O → Prop) (g f : C → O → ℝ)
    (hg : ∀ c x, 0 ≤ g c x) (hf : ∀ c x, 0 ≤ f c x)
    (hgs : ∀ c x, ¬adj c x → g c x = 0)
    (hfs : ∀ c x, ¬adj c x → f c x = 0)
    (hgr : ∀ c, rowLoad g c ≤ 1) (hgc : ∀ x, colLoad g x ≤ 1)
    (hrow : ∀ c, rowLoad g c = 0 ∨ rowLoad f c = 0)
    (hcol : ∀ x, colLoad g x = 0 ∨ colLoad f x = 0) :
    ∃ M : R2Cut.Graph (C ⊕ O),
      M ⊆ R7GraphMatrix.graphEdges adj ∧ R2Cut.Matching M ∧
      mass g + (∑ x, min (colLoad f x) 1) -
        (∑ c, max (rowLoad f c - 1) 0) ≤ (M.card : ℝ) := by
  obtain ⟨M, hM, hm, hval⟩ := R7GraphMatrix.matrix_rounding adj (withGates g f)
    (withGates_nonneg g f hg hf) (withGates_support adj g f hf hgs hfs)
    (withGates_row g f hf hgr hrow) (withGates_col g f hf hgc hcol)
  have hlow := repaired_mass_lower_columns f hf
  change mass (withGates g f) ≤ (M.card : ℝ) at hval
  rw [withGates_mass] at hval
  exact ⟨M, hM, hm, by linarith⟩

theorem gated_repair_rank [DecidableEq C] [DecidableEq O]
    (adj : C → O → Prop) (g f : C → O → ℝ)
    (hg : ∀ c x, 0 ≤ g c x) (hf : ∀ c x, 0 ≤ f c x)
    (hgs : ∀ c x, ¬adj c x → g c x = 0)
    (hfs : ∀ c x, ¬adj c x → f c x = 0)
    (hgr : ∀ c, rowLoad g c ≤ 1) (hgc : ∀ x, colLoad g x ≤ 1)
    (hrow : ∀ c, rowLoad g c = 0 ∨ rowLoad f c = 0)
    (hcol : ∀ x, colLoad g x = 0 ∨ colLoad f x = 0) :
    mass g + (∑ x, min (colLoad f x) 1) -
        (∑ c, max (rowLoad f c - 1) 0) ≤
      (R2Cut.rank (R7GraphMatrix.graphEdges adj) : ℝ) := by
  obtain ⟨M, hM, hm, hval⟩ :=
    gated_repair_matching adj g f hg hf hgs hfs hgr hgc hrow hcol
  exact hval.trans (by exact_mod_cast R2Cut.matching_card_le_rank hM hm)

/-- Lipschitz lower estimate needed to pass from a local receiver-load
event to a clipped outside contribution. -/
lemma min_lower_event {actual target err : ℝ}
    (he : 0 ≤ err) (h : target - err ≤ actual) :
    min target 1 - err ≤ min actual 1 := by
  apply le_min
  · linarith [min_le_left target 1]
  · linarith [min_le_right target 1]

lemma scaled_min (target h : ℝ) (hh : 0 < h) :
    min (target / h) 1 = min target h / h := by
  rw [← min_div_div_right hh.le]
  simp [ne_of_gt hh]

/-- A positive-availability receiver contributes its capped deterministic
load divided by availability, less the stated local error. -/
lemma scaled_receiver_lower {actual load h err : ℝ}
    (hh : 0 < h) (he : 0 ≤ err) (hlocal : load / h - err ≤ actual) :
    min load h / h - err ≤ min actual 1 := by
  rw [← scaled_min load h hh]
  exact min_lower_event he hlocal

def receiverTarget (live : O → Prop) (load cap : O → ℝ) (x : O) : ℝ :=
  if live x then min (load x) (cap x) / cap x else 0

omit [Fintype O] in
lemma receiver_target_lower (f : C → O → ℝ) (hf : ∀ c x, 0 ≤ f c x)
    (live : O → Prop) (load cap err : O → ℝ)
    (he : ∀ x, 0 ≤ err x)
    (hc : ∀ x, live x → 0 < cap x)
    (hl : ∀ x, live x → load x / cap x - err x ≤ colLoad f x) (x : O) :
    receiverTarget live load cap x - err x ≤ min (colLoad f x) 1 := by
  unfold receiverTarget
  split_ifs with hx
  · exact scaled_receiver_lower (hc x hx) (he x) (hl x hx)
  · have hcol : 0 ≤ colLoad f x := Finset.sum_nonneg fun c _ => hf c x
    have hm : 0 ≤ min (colLoad f x) 1 := le_min hcol (by norm_num)
    linarith [he x]

omit [Fintype C] in
lemma center_overload_upper (f : C → O → ℝ) (err : C → ℝ)
    (he : ∀ c, 0 ≤ err c) (hl : ∀ c, rowLoad f c ≤ 1 + err c) (c : C) :
    max (rowLoad f c - 1) 0 ≤ err c := by
  exact max_le (by linarith [hl c]) (he c)

/-- Actual graph bound on a specified local-event realization. The only
numerical hypotheses are individual sender upper loads and individual
live-receiver lower loads, the events proved by concentration separately. -/
theorem gated_rank_of_local_events [DecidableEq C] [DecidableEq O]
    (adj : C → O → Prop) (g f : C → O → ℝ)
    (hg : ∀ c x, 0 ≤ g c x) (hf : ∀ c x, 0 ≤ f c x)
    (hgs : ∀ c x, ¬adj c x → g c x = 0)
    (hfs : ∀ c x, ¬adj c x → f c x = 0)
    (hgr : ∀ c, rowLoad g c ≤ 1) (hgc : ∀ x, colLoad g x ≤ 1)
    (hrow : ∀ c, rowLoad g c = 0 ∨ rowLoad f c = 0)
    (hcol : ∀ x, colLoad g x = 0 ∨ colLoad f x = 0)
    (live : O → Prop) (load cap errO : O → ℝ) (errC : C → ℝ)
    (heO : ∀ x, 0 ≤ errO x) (heC : ∀ c, 0 ≤ errC c)
    (hc : ∀ x, live x → 0 < cap x)
    (hlO : ∀ x, live x → load x / cap x - errO x ≤ colLoad f x)
    (hlC : ∀ c, rowLoad f c ≤ 1 + errC c) :
    mass g + (∑ x, receiverTarget live load cap x) -
      (∑ x, errO x) - (∑ c, errC c) ≤
      (R2Cut.rank (R7GraphMatrix.graphEdges adj) : ℝ) := by
  have hr := gated_repair_rank adj g f hg hf hgs hfs hgr hgc hrow hcol
  have ho := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset O)) =>
    receiver_target_lower f hf live load cap errO heO hc hlO x)
  have hcc := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset C)) =>
    center_overload_upper f errC heC hlC c)
  rw [Finset.sum_sub_distrib] at ho
  linarith

end RobustMatching.R7ClosedRepair.Typed
