import RandomOrderMatching.Acquisition.CanonicalBatches
import RandomOrderMatching.Unfolding.CanonicalCopies
import RandomOrderMatching.Phases.Execution.Relabel

/-! The actual canonical copied benchmark.  The matching and exact-cardinality
claims are transported from the previously proved bipartite unfolding theorem;
the disjoint original matching endpoints make that transport injective even
when the original ambient graph is not bipartite. -/
noncomputable section
open scoped BigOperators
open Classical
set_option linter.unusedSectionVars false
namespace RandomOrderMatching.Analysis.FixedHost.Benchmark
open RandomOrderMatching.Graph RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Acquisition RandomOrderMatching.Phases.Execution
open RandomOrderMatching.Graph.BipartiteEncoding RandomOrderMatching.Graph.BipartiteMatrix
open RandomOrderMatching.Unfolding
variable {V : Type*} [Fintype V] [DecidableEq V]

def copiedBenchmark (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W)
    (M : Graph V) : Graph (V × Fin W) :=
  seenCopies (canonicalCopies W w hw) M.toList

def diagonal (M : Graph V) : Finset (M × M) :=
  Finset.univ.image (fun e : M => (e,e))

theorem diagonal_matching (M : Graph V) : RandomOrderMatching.Graph.BipartiteDual.IsMatching (diagonal M) := by
  constructor
  · intro a ha b hb hab
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hb
    simpa using congrArg (fun e : M => (e,e)) hab
  · intro a ha b hb hab
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hb
    simpa using congrArg (fun e : M => (e,e)) hab

def copyVertex (M : Graph V) (W : ℕ) : (M × Fin W) ⊕ (M × Fin W) → V × Fin W
  | .inl (e,i) => (endpoint e.val 0,i)
  | .inr (e,i) => (endpoint e.val 1,i)

theorem matching_endpoints_injective (M : Graph V) (hM : Matching M)
    {e f : M} {i j : Fin 2} (h : endpoint e.val i = endpoint f.val j) :
    e = f ∧ i = j := by
  have hh := matchingCoordinateMap_injective M hM
    (show matchingCoordinateMap M (.inl (e,i)) = matchingCoordinateMap M (.inl (f,j)) from h)
  exact Prod.mk.inj (Sum.inl.inj hh)

theorem copyVertex_injective (M : Graph V) (hM : Matching M) (W : ℕ) :
    Function.Injective (copyVertex M W) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have he := (matching_endpoints_injective M hM (congrArg Prod.fst h)).1
      have hi := congrArg Prod.snd h
      exact congrArg Sum.inl (Prod.ext he hi)
    | inr y =>
      have he := (matching_endpoints_injective M hM (congrArg Prod.fst h)).2
      norm_num at he
  | inr x =>
    cases y with
    | inl y =>
      have he := (matching_endpoints_injective M hM (congrArg Prod.fst h)).2
      norm_num at he
    | inr y =>
      have he := (matching_endpoints_injective M hM (congrArg Prod.fst h)).1
      have hi := congrArg Prod.snd h
      exact congrArg Sum.inr (Prod.ext he hi)

def nativeCopy (M : Graph V) (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W)
    (e : M) (i : Fin (w e.val)) : (M × Fin W) × (M × Fin W) :=
  ((e,⟨i.val,lt_of_lt_of_le i.isLt (hw e.val)⟩),
   (e,⟨w e.val-1-i.val,by have := hw e.val; have := i.isLt; omega⟩))

theorem nativeCopy_mem (M : Graph V) (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W)
    (e : M) (i : Fin (w e.val)) :
    nativeCopy M W w hw e i ∈ fullCopies W (diagonal M) (fun p => w p.1.val) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩
  · have := i.isLt
    dsimp [nativeCopy]
    omega

theorem nativeCopy_surjective (M : Graph V) (W : ℕ) (w : Edge V → ℕ)
    (hw : ∀ e, w e ≤ W) (f : (M × Fin W) × (M × Fin W))
    (hf : f ∈ fullCopies W (diagonal M) (fun p => w p.1.val)) :
    ∃ e i, nativeCopy M W w hw e i = f := by
  have hp := fullCopies_parent W (diagonal M) (fun p => w p.1.val) f hf
  obtain ⟨e,_,he⟩ := Finset.mem_image.mp hp
  have hL : e = f.1.1 := congrArg Prod.fst he
  have hR : e = f.2.1 := congrArg Prod.snd he
  have hi := fullCopies_indices W (diagonal M) (fun p => w p.1.val) f hf
  change f.1.2.val + f.2.2.val + 1 = w f.1.1.val at hi
  have hil : f.1.2.val < w e.val := by rw [hL]; omega
  refine ⟨e,⟨f.1.2.val,hil⟩,?_⟩
  apply Prod.ext
  · exact Prod.ext hL (Fin.ext rfl)
  · apply Prod.ext hR
    apply Fin.ext
    dsimp [nativeCopy]
    rw [hL]
    omega

theorem map_nativeCopy (M : Graph V) (hM : Matching M) (W : ℕ)
    (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W) (e : M) (i : Fin (w e.val)) :
    mapEdge (copyVertex M W) (copyVertex_injective M hM W)
      (edgeOf (nativeCopy M W w hw e i)) = canonicalCopy W w hw e.val i := by
  apply Subtype.ext
  simp [mapEdge,edgeOf,nativeCopy,copyVertex,canonicalCopy]

theorem copiedBenchmark_eq_relabel (M : Graph V) (hM : Matching M) (W : ℕ)
    (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W) :
    copiedBenchmark W w hw M =
      mapGraph (copyVertex M W) (copyVertex_injective M hM W)
        (encode (fullCopies W (diagonal M) (fun p => w p.1.val))) := by
  ext f
  simp only [copiedBenchmark,seenCopies,List.mem_toFinset,List.mem_flatMap,
    canonicalCopies,List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and,
    mapGraph,encode,Finset.mem_image]
  constructor
  · rintro ⟨e,he,i,rfl⟩
    let ee : M := ⟨e,he⟩
    refine ⟨edgeOf (nativeCopy M W w hw ee i),?_,map_nativeCopy M hM W w hw ee i⟩
    exact ⟨nativeCopy M W w hw ee i,nativeCopy_mem M W w hw ee i,rfl⟩
  · rintro ⟨g,⟨f,hmem,rfl⟩,rfl⟩
    obtain ⟨e,i,rfl⟩ := nativeCopy_surjective M W w hw f hmem
    exact ⟨e.val,e.property,i,(map_nativeCopy M hM W w hw e i).symm⟩

/-- Concrete matching and exact weight, including zero weights and W=0. -/
theorem copiedBenchmark_exact (M : Graph V) (hM : Matching M) (W : ℕ)
    (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W) :
    Matching (copiedBenchmark W w hw M) ∧
      (copiedBenchmark W w hw M).card = ∑ e ∈ M, w e := by
  have hn := matching_unfolds_exactly W (diagonal M) (fun p => w p.1.val)
    (diagonal_matching M) (fun p _ => hw p.1.val)
  rw [copiedBenchmark_eq_relabel M hM]
  constructor
  · exact (mapGraph_matching_iff _ _ _).mpr ((encode_matching_iff _).mpr hn.1)
  · rw [mapGraph_card,encode_card,hn.2]
    rw [diagonal,Finset.sum_image (by intro a _ b _ h; exact congrArg Prod.fst h)]
    exact Finset.sum_coe_sort M w

/-- Every actual copied benchmark edge retains an original benchmark parent. -/
theorem copiedBenchmark_parent_mem (M : Graph V) (W : ℕ)
    (w : Edge V → ℕ) (hw : ∀ e, w e ≤ W) (fallback : Edge V)
    {f : Edge (V × Fin W)} (hf : f ∈ copiedBenchmark W w hw M) :
    canonicalParent W fallback f ∈ M := by
  have hh := seenCopies_parent (canonicalBatchModel W w hw fallback) M.toList hf
  simpa only [canonicalBatchModel,Finset.mem_toList] using hh

end RandomOrderMatching.Analysis.FixedHost.Benchmark
