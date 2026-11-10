import RobustMatching.R7CopyDualHungarian
import RobustMatching.R7CopyDualClipped

/-! Actual two-layer bipartite graph and price extraction. This reduces a
hereditary deletion inequality on actual matchings to integral mixed prices;
strong duality itself is supplied by the unconditional Hall proof. -/
open scoped BigOperators
noncomputable section
namespace RobustMatching.R7CopyDual
open RobustMatching.Dual
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def layerEdge (a b : Bool) (e : L × R) : (Bool × L) × (Bool × R) :=
  ((a,e.1),(b,e.2))

def layerParent (e : (Bool × L) × (Bool × R)) : L × R := (e.1.2,e.2.2)

def layerExtract (M : Finset ((Bool × L) × (Bool × R))) (a b : Bool) :
    Finset (L × R) := Finset.univ.filter (fun e => layerEdge a b e ∈ M)

def auxEdges (E J : Finset (L × R)) : Finset ((Bool × L) × (Bool × R)) :=
  Finset.univ.filter (fun e => if e.1.1 = e.2.1 then layerParent e ∈ E
    else e.1.1 = false ∧ layerParent e ∈ J)

def auxWeight (w d : L × R → ℕ) (e : (Bool × L) × (Bool × R)) : ℕ :=
  if e.1.1 = e.2.1 then w (layerParent e) else d (layerParent e)

@[simp] theorem mem_layerExtract (M : Finset ((Bool × L) × (Bool × R)))
    (a b : Bool) (e : L × R) : e ∈ layerExtract M a b ↔ layerEdge a b e ∈ M := by
  simp [layerExtract]

theorem layerExtract_matching (M : Finset ((Bool × L) × (Bool × R)))
    (hm : IsMatching M) (a b : Bool) : IsMatching (layerExtract M a b) := by
  constructor
  · intro e he f hf hleft
    have h := hm.1 (mem_layerExtract M a b e |>.mp he) (mem_layerExtract M a b f |>.mp hf)
      (show (layerEdge a b e).1 = (layerEdge a b f).1 from Prod.ext rfl hleft)
    exact congrArg layerParent h
  · intro e he f hf hright
    have h := hm.2 (mem_layerExtract M a b e |>.mp he) (mem_layerExtract M a b f |>.mp hf)
      (show (layerEdge a b e).2 = (layerEdge a b f).2 from Prod.ext rfl hright)
    exact congrArg layerParent h

theorem layerExtract_same_subset (M : Finset ((Bool × L) × (Bool × R)))
    (E J : Finset (L × R)) (hsub : M ⊆ auxEdges E J) (a : Bool) :
    layerExtract M a a ⊆ E := by
  intro e he
  have h := hsub ((mem_layerExtract M a a e).mp he)
  have h' := (Finset.mem_filter.mp h).2
  simpa [layerEdge,layerParent] using h'

theorem layerExtract_cross_subset (M : Finset ((Bool × L) × (Bool × R)))
    (E J : Finset (L × R)) (hsub : M ⊆ auxEdges E J) :
    layerExtract M false true ⊆ J := by
  intro e he
  have h := hsub ((mem_layerExtract M false true e).mp he)
  have h' := (Finset.mem_filter.mp h).2
  simpa [layerEdge,layerParent] using h'

theorem layerExtract_left_disjoint (M : Finset ((Bool × L) × (Bool × R)))
    (hm : IsMatching M) (a b c : Bool) (hne : b ≠ c) :
    Disjoint ((layerExtract M a b).image Prod.fst) ((layerExtract M a c).image Prod.fst) := by
  apply Finset.disjoint_left.mpr
  intro l hl hl'
  obtain ⟨e,he,hel⟩ := Finset.mem_image.mp hl
  obtain ⟨f,hf,hfl⟩ := Finset.mem_image.mp hl'
  have h := hm.1 ((mem_layerExtract M a b e).mp he) ((mem_layerExtract M a c f).mp hf)
    (show (layerEdge a b e).1 = (layerEdge a c f).1 from Prod.ext rfl (hel.trans hfl.symm))
  exact hne (congrArg (fun z => z.2.1) h)

theorem layerExtract_right_disjoint (M : Finset ((Bool × L) × (Bool × R)))
    (hm : IsMatching M) (a b c : Bool) (hne : a ≠ b) :
    Disjoint ((layerExtract M a c).image Prod.snd) ((layerExtract M b c).image Prod.snd) := by
  apply Finset.disjoint_left.mpr
  intro r hr hr'
  obtain ⟨e,he,her⟩ := Finset.mem_image.mp hr
  obtain ⟨f,hf,hfr⟩ := Finset.mem_image.mp hr'
  have h := hm.2 ((mem_layerExtract M a c e).mp he) ((mem_layerExtract M b c f).mp hf)
    (show (layerEdge a c e).2 = (layerEdge b c f).2 from Prod.ext rfl (her.trans hfr.symm))
  exact hne (congrArg (fun z => z.1.1) h)

theorem layerExtract_image (M : Finset ((Bool × L) × (Bool × R))) (a b : Bool) :
    (layerExtract M a b).image (layerEdge a b) =
      M.filter (fun f => f.1.1=a ∧ f.2.1=b) := by
  ext f
  constructor
  · intro hf
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_filter.mpr ⟨(mem_layerExtract M a b e).mp he,by simp [layerEdge]⟩
  · intro hf
    obtain ⟨hf,ha,hb⟩ := Finset.mem_filter.mp hf
    have heq : layerEdge a b (layerParent f) = f := by
      apply Prod.ext <;> apply Prod.ext <;> simp [layerEdge,layerParent,ha,hb]
    refine Finset.mem_image.mpr ⟨layerParent f,?_,heq⟩
    rw [mem_layerExtract,heq]
    exact hf

theorem layerExtract_sum (M : Finset ((Bool × L) × (Bool × R))) (a b : Bool)
    (w : L × R → ℕ) :
    (∑ e ∈ layerExtract M a b, w e) =
      ∑ f ∈ M, if f.1.1=a ∧ f.2.1=b then w (layerParent f) else 0 := by
  have hinj : Function.Injective (layerEdge (L := L) (R := R) a b) := by
    intro e f h; exact congrArg layerParent h
  have hs := Finset.sum_image (s := layerExtract M a b) (f := fun f => w (layerParent f))
    (hinj.injOn : Set.InjOn _ _)
  rw [layerExtract_image] at hs
  simpa [layerParent,layerEdge,Finset.sum_filter] using hs.symm

theorem aux_matching_weight_split (M : Finset ((Bool × L) × (Bool × R)))
    (E J : Finset (L × R)) (w d : L × R → ℕ) (hsub : M ⊆ auxEdges E J) :
    (∑ f ∈ M, auxWeight w d f) =
      (∑ e ∈ layerExtract M false false, w e) +
      (∑ e ∈ layerExtract M true true, w e) +
      (∑ e ∈ layerExtract M false true, d e) := by
  rw [layerExtract_sum,layerExtract_sum,layerExtract_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  have h := hsub hf
  cases hL : f.1.1 <;> cases hR : f.2.1 <;>
    simp_all [auxWeight,auxEdges]

omit [Fintype L] [Fintype R] in
theorem matching_union_of_endpoint_disjoint (M N : Finset (L × R))
    (hM : IsMatching M) (hN : IsMatching N)
    (hL : Disjoint (M.image Prod.fst) (N.image Prod.fst))
    (hR : Disjoint (M.image Prod.snd) (N.image Prod.snd)) : IsMatching (M ∪ N) := by
  constructor
  · intro e he f hf h
    rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
    · exact hM.1 he hf h
    · exact False.elim (Finset.disjoint_left.mp hL (Finset.mem_image_of_mem _ he)
        (h ▸ Finset.mem_image_of_mem _ hf))
    · exact False.elim (Finset.disjoint_left.mp hL (h ▸ Finset.mem_image_of_mem _ hf)
        (Finset.mem_image_of_mem _ he))
    · exact hN.1 he hf h
  · intro e he f hf h
    rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
    · exact hM.2 he hf h
    · exact False.elim (Finset.disjoint_left.mp hR (Finset.mem_image_of_mem _ he)
        (h ▸ Finset.mem_image_of_mem _ hf))
    · exact False.elim (Finset.disjoint_left.mp hR (h ▸ Finset.mem_image_of_mem _ hf)
        (Finset.mem_image_of_mem _ he))
    · exact hN.2 he hf h

omit [Fintype L] [Fintype R] in
theorem layerLift_matching (M : Finset (L × R)) (hM : IsMatching M) (a b : Bool) :
    IsMatching (M.image (layerEdge a b)) := by
  constructor
  · intro e he f hf h
    obtain ⟨e,heM,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f,hfM,rfl⟩ := Finset.mem_image.mp hf
    have hef := hM.1 heM hfM (congrArg (fun z : Bool × L => z.2) h)
    exact congrArg (layerEdge a b) hef
  · intro e he f hf h
    obtain ⟨e,heM,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f,hfM,rfl⟩ := Finset.mem_image.mp hf
    have hef := hM.2 heM hfM (congrArg (fun z : Bool × R => z.2) h)
    exact congrArg (layerEdge a b) hef

omit [Fintype L] [Fintype R] in
theorem layerLift_left_disjoint (M N : Finset (L × R)) (a b c d : Bool)
    (h : a ≠ c ∨ Disjoint (M.image Prod.fst) (N.image Prod.fst)) :
    Disjoint ((M.image (layerEdge a b)).image Prod.fst)
      ((N.image (layerEdge c d)).image Prod.fst) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hz
  obtain ⟨f,hf,hfq⟩ := Finset.mem_image.mp hz'
  obtain ⟨e,heM,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨f,hfN,rfl⟩ := Finset.mem_image.mp hf
  have hpair := heq.trans hfq.symm
  rcases h with h | h
  · exact h (congrArg Prod.fst hpair)
  · have hl : e.1=f.1 := congrArg (fun z : Bool × L => z.2) hpair
    have hf' : e.1 ∈ N.image Prod.fst := by rw [hl]; exact Finset.mem_image_of_mem _ hfN
    exact Finset.disjoint_left.mp h (Finset.mem_image_of_mem _ heM) hf'

omit [Fintype L] [Fintype R] in
theorem layerLift_right_disjoint (M N : Finset (L × R)) (a b c d : Bool)
    (h : b ≠ d ∨ Disjoint (M.image Prod.snd) (N.image Prod.snd)) :
    Disjoint ((M.image (layerEdge a b)).image Prod.snd)
      ((N.image (layerEdge c d)).image Prod.snd) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hz
  obtain ⟨f,hf,hfq⟩ := Finset.mem_image.mp hz'
  obtain ⟨e,heM,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨f,hfN,rfl⟩ := Finset.mem_image.mp hf
  have hpair := heq.trans hfq.symm
  rcases h with h | h
  · exact h (congrArg Prod.fst hpair)
  · have hr : e.2=f.2 := congrArg (fun z : Bool × R => z.2) hpair
    have hf' : e.2 ∈ N.image Prod.snd := by rw [hr]; exact Finset.mem_image_of_mem _ hfN
    exact Finset.disjoint_left.mp h (Finset.mem_image_of_mem _ heM) hf'

/-- Every pair of deletion matchings and selected cross matching is realized
by one actual auxiliary matching with exactly the sum of their weights. -/
theorem realize_deletion_matchings (E J M1 M2 T : Finset (L × R)) (w d : L × R → ℕ)
    (h1 : IsMatching M1) (h2 : IsMatching M2) (hT : IsMatching T)
    (hs1 : M1 ⊆ E) (hs2 : M2 ⊆ E) (hsT : T ⊆ J)
    (hd1 : Disjoint (M1.image Prod.fst) (T.image Prod.fst))
    (hd2 : Disjoint (M2.image Prod.snd) (T.image Prod.snd)) :
    ∃ M : Finset ((Bool × L) × (Bool × R)), IsMatching M ∧ M ⊆ auxEdges E J ∧
      (∑ f ∈ M, auxWeight w d f)=
        (∑ e ∈ M1, w e)+(∑ e ∈ M2, w e)+(∑ e ∈ T, d e) := by
  let A:=M1.image (layerEdge false false)
  let B:=M2.image (layerEdge true true)
  let C:=T.image (layerEdge false true)
  have habL := layerLift_left_disjoint M1 M2 false false true true (Or.inl (by decide))
  have habR := layerLift_right_disjoint M1 M2 false false true true (Or.inl (by decide))
  have hacL := layerLift_left_disjoint M1 T false false false true (Or.inr hd1)
  have hbcL := layerLift_left_disjoint M2 T true true false true (Or.inl (by decide))
  have hacR := layerLift_right_disjoint M1 T false false false true (Or.inl (by decide))
  have hbcR := layerLift_right_disjoint M2 T true true false true (Or.inr hd2)
  have hab : IsMatching (A ∪ B) := matching_union_of_endpoint_disjoint A B
    (layerLift_matching M1 h1 false false) (layerLift_matching M2 h2 true true) habL habR
  have hallL : Disjoint ((A ∪ B).image Prod.fst) (C.image Prod.fst) := by
    rw [Finset.image_union]; exact Finset.disjoint_union_left.mpr ⟨hacL,hbcL⟩
  have hallR : Disjoint ((A ∪ B).image Prod.snd) (C.image Prod.snd) := by
    rw [Finset.image_union]; exact Finset.disjoint_union_left.mpr ⟨hacR,hbcR⟩
  refine ⟨A ∪ B ∪ C,matching_union_of_endpoint_disjoint (A ∪ B) C hab
    (layerLift_matching T hT false true) hallL hallR,?_,?_⟩
  · intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · rcases Finset.mem_union.mp hf with hf | hf
      · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,by simpa [layerEdge,layerParent] using hs1 he⟩
      · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,by simpa [layerEdge,layerParent] using hs2 he⟩
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simpa [layerEdge,layerParent] using hsT he⟩
  · rw [Finset.sum_union (Disjoint.of_image_finset hallL),
      Finset.sum_union (Disjoint.of_image_finset habL)]
    have hinj (a b : Bool) : Function.Injective (layerEdge (L := L) (R := R) a b) := by
      intro e f h; exact congrArg layerParent h
    simp only [C,Finset.sum_image (hinj false false).injOn,
      Finset.sum_image (hinj true true).injOn,Finset.sum_image (hinj false true).injOn]
    simp [auxWeight,layerEdge,layerParent]

/-- Extract two integral price vectors from a hereditary bound on the
three actual matchings selected by the auxiliary graph. -/
theorem two_layer_prices_of_deletion_bound (E J : Finset (L × R))
    (w d : L × R → ℕ) (B : ℕ)
    (hbound : ∀ M1 M2 T : Finset (L × R), IsMatching M1 → IsMatching M2 → IsMatching T →
      M1 ⊆ E → M2 ⊆ E → T ⊆ J →
      Disjoint (M1.image Prod.fst) (T.image Prod.fst) →
      Disjoint (M2.image Prod.snd) (T.image Prod.snd) →
      (∑ e ∈ M1, w e) + (∑ e ∈ M2, w e) + (∑ e ∈ T, d e) ≤ B) :
    ∃ (p1 p2 : L → ℕ) (q1 q2 : R → ℕ),
      (∀ e ∈ E, w e ≤ p1 e.1 + q1 e.2) ∧
      (∀ e ∈ E, w e ≤ p2 e.1 + q2 e.2) ∧
      (∀ e ∈ J, d e ≤ p1 e.1 + q2 e.2) ∧
      (∑ l, p1 l) + (∑ r, q1 r) + (∑ l, p2 l) + (∑ r, q2 r) ≤ B := by
  obtain ⟨M,p,q,hm,hsub,hfeas,hcost⟩ := exists_nat_bipartite_dual (auxEdges E J) (auxWeight w d)
  have hb := hbound (layerExtract M false false) (layerExtract M true true) (layerExtract M false true)
    (layerExtract_matching M hm false false) (layerExtract_matching M hm true true)
    (layerExtract_matching M hm false true) (layerExtract_same_subset M E J hsub false)
    (layerExtract_same_subset M E J hsub true) (layerExtract_cross_subset M E J hsub)
    (layerExtract_left_disjoint M hm false false true (by decide))
    (layerExtract_right_disjoint M hm true false true (by decide))
  rw [← aux_matching_weight_split M E J w d hsub,hcost] at hb
  refine ⟨fun l => p (false,l), fun l => p (true,l),
    fun r => q (false,r), fun r => q (true,r), ?_,?_,?_,?_⟩
  · intro e he
    have hmem : layerEdge false false e ∈ auxEdges E J := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simp [layerEdge,layerParent,he]⟩
    have h := hfeas (layerEdge false false e) hmem
    simpa [auxWeight,layerEdge,layerParent] using h
  · intro e he
    have hmem : layerEdge true true e ∈ auxEdges E J := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simp [layerEdge,layerParent,he]⟩
    have h := hfeas (layerEdge true true e) hmem
    simpa [auxWeight,layerEdge,layerParent] using h
  · intro e he
    have hmem : layerEdge false true e ∈ auxEdges E J := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simp [layerEdge,layerParent,he]⟩
    have h := hfeas (layerEdge false true e) hmem
    simpa [auxWeight,layerEdge,layerParent] using h
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hb
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb

/-- Complete copy/duality bridge from a hereditary *actual matching*
deletion bound. The only external structural input is hbound; integral
prices, auxiliary decomposition, copy matching and clipped loss are proved.
Instantiate hbound with the sharp general-graph theorem to obtain the
phase inequality. -/
theorem clipped_copies_of_deletion_bound
    (W : ℕ) (E J : Finset (L × R)) (wA wJ delta : L × R → ℕ) (B : ℕ)
    (hJ : IsMatching J)
    (hbound : ∀ M1 M2 T : Finset (L × R), IsMatching M1 → IsMatching M2 → IsMatching T →
      M1 ⊆ E → M2 ⊆ E → T ⊆ J →
      Disjoint (M1.image Prod.fst) (T.image Prod.fst) →
      Disjoint (M2.image Prod.snd) (T.image Prod.snd) →
      (∑ e ∈ M1, wA e) + (∑ e ∈ M2, wA e) + (∑ e ∈ T, (wJ e-delta e)) ≤ B)
    (C1 C2 S : Finset ((L × Fin W) × (R × Fin W)))
    (hc1 : IsMatching C1) (hc2 : IsMatching C2)
    (hs1 : ∀ e ∈ C1, e ∈ RobustMatching.R6FableSharpDualCopy.CopyEdges W (E : Set _) wA)
    (hs2 : ∀ e ∈ C2, e ∈ RobustMatching.R6FableSharpDualCopy.CopyEdges W (E : Set _) wA)
    (hsub : ∀ e ∈ S, parent e ∈ J)
    (hd1 : Disjoint (C1.image Prod.fst) (S.image Prod.fst))
    (hd2 : Disjoint (C2.image Prod.snd) (S.image Prod.snd))
    (hidx : ∀ e ∈ S, e.1.2.val+e.2.2.val+1=wJ (parent e)) :
    C1.card+C2.card+S.card ≤ B+∑ e ∈ J, min (rootFiber S e).card (delta e) := by
  obtain ⟨p1,p2,q1,q2,h1,h2,hmix,hcost⟩ :=
    two_layer_prices_of_deletion_bound E J wA (fun e => wJ e-delta e) B hbound
  have hmix' : ∀ e ∈ J, wJ e ≤ p1 e.1+q2 e.2+delta e := by
    intro e he
    have h := hmix e he
    omega
  have h := clipped_copy_deletion_bound W (E : Set _) J wA wJ delta p1 p2 q1 q2
    h1 h2 C1 C2 S hc1 hc2 hJ hs1 hs2 hsub hd1 hd2 hidx hmix'
  have hb : ((∑ l, (p1 l : ℝ))+(∑ r, (q1 r : ℝ)))+
      ((∑ l, (p2 l : ℝ))+(∑ r, (q2 r : ℝ))) ≤ (B : ℝ) := by
    have hh : (∑ l, p1 l)+(∑ r, q1 r)+((∑ l, p2 l)+(∑ r, q2 r)) ≤ B := by omega
    exact_mod_cast hh
  have hc : (C1.card : ℝ)+C2.card+S.card ≤
      (B : ℝ)+∑ e ∈ J, (min (rootFiber S e).card (delta e) : ℝ) := by linarith
  exact_mod_cast hc

end RobustMatching.R7CopyDual
#print axioms RobustMatching.R7CopyDual.two_layer_prices_of_deletion_bound
#print axioms RobustMatching.R7CopyDual.clipped_copies_of_deletion_bound
