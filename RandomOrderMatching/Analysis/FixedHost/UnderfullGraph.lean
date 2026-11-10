import RandomOrderMatching.Acquisition.Provenance

/-! Frozen underfull suffix edges, defined by projecting the actual acquisition
records. All degree statements concern the frozen reference H, never H union U. -/
noncomputable section
open Classical
set_option linter.unusedSectionVars false
namespace RandomOrderMatching.Analysis.FixedHost.Eligibility
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition
variable {V E : Type*} [Fintype V] [DecidableEq V]

def underfullSuffix (lower : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (suffix : List E) : Graph V :=
  (underfullRecords lower H (suffix.flatMap batch) 0).image Prod.fst

def availableSuffix (lower : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (suffix : List E) : Graph V := H ∪ underfullSuffix lower H batch suffix

def eligibleOriginal (lower : ℕ) (H : Graph V) (batch : E → List (Edge V)) (a : E) : Prop :=
  ∃ f ∈ batch a, edgeDegree H f < lower

def referenceParents [DecidableEq E] (parent : Edge V → E) (H : Graph V) : Finset E :=
  H.image parent

theorem underfullSuffix_eq_filter (lower : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (suffix : List E) :
    underfullSuffix lower H batch suffix =
      (seenCopies batch suffix).filter (fun f => edgeDegree H f < lower) := by
  simp [underfullSuffix,underfullRecords,seenCopies,Finset.image_image,Function.comp_def]

theorem mem_underfullSuffix (lower : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (suffix : List E) (f : Edge V) :
    f ∈ underfullSuffix lower H batch suffix ↔
      f ∈ seenCopies batch suffix ∧ edgeDegree H f < lower := by
  rw [underfullSuffix_eq_filter,Finset.mem_filter]

theorem seenCopies_mono [DecidableEq E] (batch : E → List (Edge V))
    {xs ys : List E} (h : xs.toFinset ⊆ ys.toFinset) :
    seenCopies batch xs ⊆ seenCopies batch ys := by
  intro f hf
  obtain ⟨a,ha,hfa⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hf)
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
    ⟨a,List.mem_toFinset.mp (h (List.mem_toFinset.mpr ha)),hfa⟩)

theorem underfullSuffix_subset (lower : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (suffix : List E) : underfullSuffix lower H batch suffix ⊆ seenCopies batch suffix := by
  intro f hf
  exact ((mem_underfullSuffix lower H batch suffix f).mp hf).1

theorem availableSuffix_subset (lower : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (suffix : List E) :
    availableSuffix lower H batch suffix ⊆ H ∪ seenCopies batch suffix := by
  exact Finset.union_subset_union_right (underfullSuffix_subset lower H batch suffix)

/-- The bound is on degrees in H, including for edges of H union U. -/
theorem availableSuffix_upper (lower beta : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (suffix : List E) (hH : Upper beta H) (hlower : lower ≤ beta) :
    ∀ f ∈ availableSuffix lower H batch suffix, edgeDegree H f ≤ beta := by
  intro f hf
  rcases Finset.mem_union.mp hf with hf | hf
  · exact hH f hf
  · exact (Nat.le_of_lt ((mem_underfullSuffix lower H batch suffix f).mp hf).2).trans hlower

theorem availableSuffix_upper_real (lower : ℕ) (beta : ℝ) (H : Graph V)
    (batch : E → List (Edge V)) (suffix : List E)
    (hH : ∀ f ∈ H, (edgeDegree H f : ℝ) ≤ beta) (hlower : (lower : ℝ) ≤ beta) :
    ∀ f ∈ availableSuffix lower H batch suffix, (edgeDegree H f : ℝ) ≤ beta := by
  intro f hf
  rcases Finset.mem_union.mp hf with hf | hf
  · exact hH f hf
  · have hd := ((mem_underfullSuffix lower H batch suffix f).mp hf).2
    have hc : (edgeDegree H f : ℝ) < lower := by exact_mod_cast hd
    exact hc.le.trans hlower

theorem missing_lower (lower : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (suffix : List E) {f : Edge V} (hseen : f ∈ seenCopies batch suffix)
    (hmissing : f ∉ availableSuffix lower H batch suffix) : lower ≤ edgeDegree H f := by
  by_contra h
  have hd : edgeDegree H f < lower := Nat.lt_of_not_ge h
  apply hmissing
  exact Finset.mem_union_right H ((mem_underfullSuffix lower H batch suffix f).mpr ⟨hseen,hd⟩)

theorem missing_subgraph_lower (lower : ℕ) (H : Graph V) (batch : E → List (Edge V))
    (suffix : List E) (M : Graph V) (hM : M ⊆ seenCopies batch suffix) :
    ∀ f ∈ M \ availableSuffix lower H batch suffix, lower ≤ edgeDegree H f := by
  intro f hf
  exact missing_lower lower H batch suffix (hM (Finset.mem_sdiff.mp hf).1) (Finset.mem_sdiff.mp hf).2

theorem underfullSuffix_parent (lower : ℕ) (H : Graph V) (model : BatchModel E V)
    (suffix : List E) {f : Edge V} (hf : f ∈ underfullSuffix lower H model.copies suffix) :
    model.parent f ∈ suffix ∧ eligibleOriginal lower H model.copies (model.parent f) := by
  obtain ⟨hseen,hd⟩ := (mem_underfullSuffix lower H model.copies suffix f).mp hf
  obtain ⟨a,ha,hfa⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hseen)
  rw [model.parent_mem a f hfa]
  exact ⟨ha,f,hfa,hd⟩

theorem availableSuffix_parent [DecidableEq E] (lower : ℕ) (H : Graph V)
    (model : BatchModel E V) (suffix : List E) {f : Edge V}
    (hf : f ∈ availableSuffix lower H model.copies suffix) :
    model.parent f ∈ referenceParents model.parent H ∨
      (eligibleOriginal lower H model.copies (model.parent f) ∧ model.parent f ∈ suffix) := by
  rcases Finset.mem_union.mp hf with hf | hf
  · exact Or.inl (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
  · have hh := underfullSuffix_parent lower H model suffix hf
    exact Or.inr ⟨hh.2,hh.1⟩

end RandomOrderMatching.Analysis.FixedHost.Eligibility
