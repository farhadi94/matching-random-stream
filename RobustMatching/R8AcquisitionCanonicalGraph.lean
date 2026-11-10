import RobustMatching.R8AcquisitionCanonical
import RobustMatching.R7GraphMarked

noncomputable section
open Classical
namespace RobustMatching.R8Acquisition
open RobustMatching.R2Cut RobustMatching.R7SupportFlowMap RobustMatching.R7GraphKonig
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem canonicalCopy_pair_data (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W)
    (e : Edge V) (i : Fin (w e)) (x y : V×Fin W) (hne : x≠y)
    (hpair : (canonicalCopy W w hw e i).val={x,y}) :
    ({x.1,y.1}:Finset V)=e.val ∧ x.2.val+y.2.val+1=w e := by
  constructor
  · have hh := congrArg (Finset.image Prod.fst) hpair
    rw [canonicalCopy_projection] at hh
    simpa using hh.symm
  · have hx : x∈(canonicalCopy W w hw e i).val := by rw [hpair]; simp
    have hy : y∈(canonicalCopy W w hw e i).val := by rw [hpair]; simp
    simp only [canonicalCopy,Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hne rfl).elim
    · simp only
      have := i.isLt
      omega
    · simp only
      have := i.isLt
      omega
    · exact (hne rfl).elim

theorem canonicalCopies_contains_oriented (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W)
    (e : Edge V) (x y : V×Fin W) (hx : x.1=endpoint e 0) (hy : y.1=endpoint e 1)
    (hi : x.2.val+y.2.val+1=w e) :
    ∃ f∈canonicalCopies W w hw e,f.val={x,y} := by
  let i : Fin (w e) := ⟨x.2.val,by omega⟩
  refine ⟨canonicalCopy W w hw e i,?_,?_⟩
  · exact List.mem_map.mpr ⟨i,by simp,rfl⟩
  · have hl : ((endpoint e 0,⟨i.val,lt_of_lt_of_le i.isLt (hw e)⟩):V×Fin W)=x := by
      apply Prod.ext
      · exact hx.symm
      · apply Fin.ext; rfl
    have hr : ((endpoint e 1,⟨w e-1-i.val,by have := hw e; have := i.isLt; omega⟩):V×Fin W)=y := by
      apply Prod.ext
      · exact hy.symm
      · apply Fin.ext
        dsimp [i]
        omega
    change {_,_}=({x,y}:Finset (V×Fin W))
    rw [hl,hr]

theorem canonicalCopies_pair_iff (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W)
    (e : Edge V) (x y : V×Fin W) (hne : x≠y) :
    (∃ f∈canonicalCopies W w hw e,f.val={x,y}) ↔
      ({x.1,y.1}:Finset V)=e.val ∧ x.2.val+y.2.val+1=w e := by
  constructor
  · rintro ⟨f,hf,hpair⟩
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact canonicalCopy_pair_data W w hw e i x y hne hpair
  · rintro ⟨hpair,hi⟩
    have hx : x.1∈({endpoint e 0,endpoint e 1}:Finset V) := by rw [endpoint_pair,←hpair]; simp
    have hy : y.1∈({endpoint e 0,endpoint e 1}:Finset V) := by rw [endpoint_pair,←hpair]; simp
    have hn : x.1≠y.1 := by
      intro h
      have hc := congrArg Finset.card hpair
      simp [h,e.property] at hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (hn (hx.trans hy.symm)).elim
    · exact canonicalCopies_contains_oriented W w hw e x y hx hy hi
    · obtain ⟨f,hf,hxy⟩ := canonicalCopies_contains_oriented W w hw e y x hy hx (by omega)
      exact ⟨f,hf,hxy.trans (Finset.pair_comm _ _)⟩
    · exact (hn (hx.trans hy.symm)).elim

/-- Enumerating the actual canonical batches produces exactly the pre-existing
canonical unfolding, with one physical parent label per input edge. -/
theorem canonical_seenCopies_eq_unfolding (G : Graph V) (W : ℕ) (w : Sym2 V → ℕ)
    (hw : ∀ e : Edge V,w (canonicalEdgeSym e)≤W) (labels : List (Edge V))
    (hlabels : labels.toFinset=G) :
    simpleGraph (seenCopies (canonicalCopies W (fun e=>w (canonicalEdgeSym e)) hw) labels)=
      R8BalancedCut.unfolding (simpleGraph G) w W := by
  ext x y
  constructor
  · rintro ⟨⟨f,hf,hpair⟩,hne⟩
    obtain ⟨e,he,hcopy⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hf)
    have hd := (canonicalCopies_pair_iff W (fun e=>w (canonicalEdgeSym e)) hw e x y hne).mp
      ⟨f,hcopy,by simpa only [Sym2.toFinset_mk_eq] using hpair.symm⟩
    have hs : s(x.1,y.1)=canonicalEdgeSym e := by
      apply sym2_toFinset_injective
      simpa only [Sym2.toFinset_mk_eq,canonicalEdgeSym_toFinset] using hd.1
    refine ⟨?_,by simpa only [hs] using hd.2⟩
    refine ⟨⟨e,?_,?_⟩,?_⟩
    · rw [←hlabels]; exact List.mem_toFinset.mpr he
    · simpa only [Sym2.toFinset_mk_eq] using hd.1
    · intro heq
      have hc := congrArg Finset.card hd.1
      simp [heq,e.property] at hc
  · rintro ⟨⟨⟨e,he,hpair⟩,hne⟩,hidx⟩
    have hxy : x≠y := by intro h; exact hne (congrArg Prod.fst h)
    have hs : s(x.1,y.1)=canonicalEdgeSym e := by
      apply sym2_toFinset_injective
      rw [canonicalEdgeSym_toFinset]
      exact hpair
    obtain ⟨f,hf,hpairf⟩ := (canonicalCopies_pair_iff W (fun e=>w (canonicalEdgeSym e)) hw e x y hxy).mpr
      ⟨by simpa only [Sym2.toFinset_mk_eq] using hpair,by simpa only [hs] using hidx⟩
    refine ⟨⟨f,?_,?_⟩,hxy⟩
    · apply List.mem_toFinset.mpr
      apply List.mem_flatMap.mpr
      refine ⟨e,?_,hf⟩
      rw [←hlabels] at he
      exact List.mem_toFinset.mp he
    · simpa only [Sym2.toFinset_mk_eq] using hpairf.symm

/-- The actual acquired H is a subgraph of the canonical unfolding; the
batch-to-unfolding correspondence is discharged here. -/
theorem canonical_run_subgraph (cfg : Config) (G : Graph V) (W : ℕ) (w : Sym2 V → ℕ)
    (hw : ∀ e : Edge V,w (canonicalEdgeSym e)≤W) (labels : List (Edge V))
    (hlabels : labels.toFinset=G) :
    simpleGraph (run cfg (canonicalCopies W (fun e=>w (canonicalEdgeSym e)) hw) labels).ref ≤
      R8BalancedCut.unfolding (simpleGraph G) w W := by
  rw [←canonical_seenCopies_eq_unfolding G W w hw labels hlabels]
  exact RobustMatching.R7GraphMarked.simpleGraph_mono (run_ref_subset cfg _ labels)



/-- Extend the actual original-edge weight function by zero on diagonal Sym2 labels. -/
def canonicalSymWeight (w : Edge V → ℕ) (q : Sym2 V) : ℕ :=
  if h : q.toFinset.card=2 then w ⟨q.toFinset,h⟩ else 0

theorem canonicalSymWeight_edge (w : Edge V → ℕ) (e : Edge V) :
    canonicalSymWeight w (canonicalEdgeSym e)=w e := by
  simp only [canonicalSymWeight,canonicalEdgeSym_toFinset,e.property,dif_pos]

theorem canonical_run_subgraph_of_original_weights (cfg : Config) (G : Graph V)
    (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W) (labels : List (Edge V))
    (hlabels : labels.toFinset=G) :
    simpleGraph (run cfg (canonicalCopies W w hw) labels).ref ≤
      R8BalancedCut.unfolding (simpleGraph G) (canonicalSymWeight w) W := by
  have hfun : (fun e=>canonicalSymWeight w (canonicalEdgeSym e))=w := by
    funext e; exact canonicalSymWeight_edge w e
  have hb : ∀ e : Edge V, canonicalSymWeight w (canonicalEdgeSym e)≤W := by
    intro e; rw [canonicalSymWeight_edge]; exact hw e
  have hh := canonical_run_subgraph cfg G W (canonicalSymWeight w) hb labels hlabels
  have hc : canonicalCopies W (fun e=>canonicalSymWeight w (canonicalEdgeSym e)) hb=canonicalCopies W w hw := by
    congr 1
  rw [hc] at hh
  exact hh


theorem canonical_run_subgraph_of_prefix (cfg : Config) (G : Graph V)
    (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W) (labels : List (Edge V))
    (hlabels : labels.toFinset⊆G) :
    simpleGraph (run cfg (canonicalCopies W w hw) labels).ref ≤
      R8BalancedCut.unfolding (simpleGraph G) (canonicalSymWeight w) W := by
  have hh := canonical_run_subgraph_of_original_weights cfg labels.toFinset W w hw labels rfl
  intro x y hxy
  have hx := hh hxy
  exact ⟨RobustMatching.R7GraphMarked.simpleGraph_mono hlabels hx.1,hx.2⟩

theorem final_underfull_iff (kappa L ell cap : ℕ) (hk : 0<kappa) (hL : 0<L) (he : 0<ell)
    (d : ℕ) :
    d<(finalAcquisitionConfig kappa L ell cap hk hL he).lower ↔
      (d:ℝ)<(1-(10:ℝ)^(-9:ℤ))*((finalAcquisitionConfig kappa L ell cap hk hL he).beta:ℝ) := by
  rw [←final_lower_exact kappa L ell cap hk hL he]
  exact_mod_cast Iff.rfl

end RobustMatching.R8Acquisition
#print axioms RobustMatching.R8Acquisition.canonical_seenCopies_eq_unfolding
#print axioms RobustMatching.R8Acquisition.canonical_run_subgraph
