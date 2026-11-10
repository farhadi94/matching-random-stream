import RobustMatching.R7GraphInterpretationDefs

/-! The union of two actual matchings is bipartite. The proof inserts
matching edges and flips actual components, without a path oracle. -/

noncomputable section
open scoped BigOperators symmDiff
open Classical

namespace RobustMatching.R7GraphInterpretation
open RobustMatching.R2Cut RobustMatching.R7GraphKonig
open RobustMatching.R7GraphComponents RobustMatching.R7GraphBipartiteExchange
open RobustMatching.R7GraphMarked

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem crosses_flip_closed {G : Graph V} {C S : Finset V}
    (hc : Crosses G C) (hS : ClosedBlock G S) : Crosses G (C ∆ S) := by
  intro e he
  rcases hS e he with hi | hd
  · have hset : e.val ∩ (C ∆ S) = e.val \ C := by
      ext v
      by_cases hv : v ∈ e.val
      · have hs := hi hv
        simp [hv,hs,Finset.mem_symmDiff]
      · simp [hv]
    rw [hset,Finset.card_sdiff,Finset.inter_comm,hc e he,e.property]
  · have hset : e.val ∩ (C ∆ S) = e.val ∩ C := by
      ext v
      by_cases hv : v ∈ e.val
      · have hs : v ∉ S := fun h => Finset.disjoint_left.mp hd hv h
        simp [hv,hs,Finset.mem_symmDiff]
      · simp [hv]
    rw [hset,hc e he]

theorem crosses_colorable {G : Graph V} {C : Finset V} (hc : Crosses G C) :
    (simpleGraph G).Colorable 2 := by
  apply colorable_of_cut G (fun v => decide (v ∈ C))
  intro e he u hu v hv hn heq
  have hm : u ∈ C ↔ v ∈ C := by simpa only [decide_eq_decide] using heq
  by_cases huC : u ∈ C
  · have h := hc e he
    exact hn (Finset.card_le_one.mp h.le u (Finset.mem_inter.mpr ⟨hu,huC⟩)
      v (Finset.mem_inter.mpr ⟨hv,hm.mp huC⟩))
  · have hvC : v ∉ C := fun hh => huC (hm.mpr hh)
    have h := crosses_compl hc e he
    exact hn (Finset.card_le_one.mp h.le u
      (Finset.mem_inter.mpr ⟨hu,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,huC⟩⟩)
      v (Finset.mem_inter.mpr ⟨hv,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hvC⟩⟩))

theorem exists_crosses_of_colorable (G : Graph V) (hc : (simpleGraph G).Colorable 2) :
    ∃ C : Finset V, Crosses G C := by
  obtain ⟨col⟩ := hc
  let C := Finset.univ.filter fun v => col v = 0
  refine ⟨C,?_⟩
  intro e he
  obtain ⟨u,v,hn,hev⟩ := Finset.card_eq_two.mp e.property
  have hadj : (simpleGraph G).Adj u v :=
    adj_of_edge he (by rw [hev]; simp) (by rw [hev]; simp) hn
  have hne := col.valid hadj
  have hu : col u = 0 ∨ col u = 1 := by omega
  have hv : col v = 0 ∨ col v = 1 := by omega
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact (hne (hu.trans hv.symm)).elim
  · have hs : e.val ∩ C = {u} := by ext x; simp [hev,C,hu,hv]
    rw [hs]; simp
  · have hs : e.val ∩ C = {v} := by ext x; simp [hev,C,hu,hv]
    rw [hs]; simp
  · exact (hne (hu.trans hv.symm)).elim

theorem insert_exposed_edge_crosses {P Q : Graph V} {e : Edge V} {C : Finset V}
    (hP : Matching P) (hQ : Matching Q) (hc : Crosses (P ∪ Q) C)
    (hex : Disjoint e.val (covered P)) :
    ∃ D : Finset V, Crosses (insert e P ∪ Q) D := by
  obtain ⟨u,v,hn,hev⟩ := Finset.card_eq_two.mp e.property
  have hu : u ∈ e.val := by rw [hev]; simp
  have hv : v ∈ e.val := by rw [hev]; simp
  have ha : Disjoint (covered P) ({u,v} : Finset V) := by
    rw [← hev]
    exact hex.symm
  have finish (D : Finset V) (hD : Crosses (P ∪ Q) D) (heD : (e.val ∩ D).card = 1) :
      Crosses (insert e P ∪ Q) D := by
    intro f hf
    rcases Finset.mem_union.mp hf with hp | hq
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · exact heD
      · exact hD f (Finset.mem_union_left _ hp)
    · exact hD f (Finset.mem_union_right _ hq)
  by_cases heC : (e.val ∩ C).card = 1
  · exact ⟨C,finish C hc heC⟩
  have hsame : u ∈ C ↔ v ∈ C := by
    by_cases huC : u ∈ C <;> by_cases hvC : v ∈ C
    · simp [huC,hvC]
    · have hh : e.val ∩ C = {u} := by ext x; simp [hev,huC,hvC]
      exact (heC (by rw [hh]; simp)).elim
    · have hh : e.val ∩ C = {v} := by ext x; simp [hev,huC,hvC]
      exact (heC (by rw [hh]; simp)).elim
    · simp [huC,hvC]
  have hnr : ¬(simpleGraph (P ∪ Q)).Reachable u v := by
    intro hr
    have hmarks : RobustMatching.R7AlgebraPath.Separated (P ∪ Q) {u,v} := by
      by_cases huC : u ∈ C
      · have hsub : ({u,v} : Finset V) ⊆ C := by
          intro x hx
          simp only [Finset.mem_insert,Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact huC
          · exact hsame.mp huC
        simpa using cut_union_separated (Finset.subset_union_left) (Finset.subset_union_right)
          hP hQ hc hsub (Finset.empty_subset _) ha (by simp)
      · have hsub : ({u,v} : Finset V) ⊆ Finset.univ \ C := by
          intro x hx
          simp only [Finset.mem_insert,Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · simp [huC]
          · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hh => huC (hsame.mpr hh)⟩
        simpa using cut_union_separated (Finset.subset_union_left) (Finset.subset_union_right)
          hP hQ (crosses_compl hc) hsub (Finset.empty_subset _) ha (by simp)
    exact hn (hmarks u (by simp) v (by simp) hr)
  let S := componentVertices (P ∪ Q) ((simpleGraph (P ∪ Q)).connectedComponentMk u)
  have huS : u ∈ S := by simp [S,componentVertices]
  have hvS : v ∉ S := by
    intro hh
    have heq : (simpleGraph (P ∪ Q)).connectedComponentMk v =
        (simpleGraph (P ∪ Q)).connectedComponentMk u := by simpa [S,componentVertices] using hh
    exact hnr (SimpleGraph.ConnectedComponent.exact heq.symm)
  have hflip := crosses_flip_closed hc
    (component_closed (P ∪ Q) ((simpleGraph (P ∪ Q)).connectedComponentMk u))
  refine ⟨C ∆ S,finish _ hflip ?_⟩
  by_cases huC : u ∈ C
  · have hvC := hsame.mp huC
    have hh : e.val ∩ (C ∆ S) = {v} := by
      ext x
      simp [hev,Finset.mem_symmDiff,huC,hvC,huS,hvS]
    rw [hh]; simp
  · have hvC : v ∉ C := fun hh => huC (hsame.mpr hh)
    have hh : e.val ∩ (C ∆ S) = {u} := by
      ext x
      simp [hev,Finset.mem_symmDiff,huC,hvC,huS,hvS]
    rw [hh]; simp

theorem matching_exists_crosses (N : Graph V) (hN : Matching N) :
    ∃ C : Finset V, Crosses N C := by
  induction N using Finset.induction_on with
  | empty => exact ⟨∅,fun e he => (Finset.notMem_empty e he).elim⟩
  | @insert e N he ih =>
      have hsmall : Matching N := matching_mono hN (Finset.subset_insert _ _)
      obtain ⟨C,hC⟩ := ih hsmall
      have hx : Disjoint e.val (covered N) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvN
        obtain ⟨f,hf,hvf⟩ := mem_covered.mp hvN
        have hne : e ≠ f := fun hh => he (hh ▸ hf)
        exact Finset.disjoint_left.mp
          (hN (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hf) hne) hv hvf
      have hc : Crosses (N ∪ ∅) C := by simpa using hC
      obtain ⟨D,hD⟩ := insert_exposed_edge_crosses hsmall
        RobustMatching.R6FableImportance.empty_matching hc hx
      exact ⟨D,by simpa using hD⟩

theorem matching_union_exists_crosses (P Q : Graph V) (hP : Matching P) (hQ : Matching Q) :
    ∃ C : Finset V, Crosses (P ∪ Q) C := by
  induction P using Finset.induction_on with
  | empty => simpa using matching_exists_crosses Q hQ
  | @insert e P he ih =>
      have hsmall : Matching P := matching_mono hP (Finset.subset_insert _ _)
      obtain ⟨C,hC⟩ := ih hsmall
      have hx : Disjoint e.val (covered P) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvP
        obtain ⟨f,hf,hvf⟩ := mem_covered.mp hvP
        have hne : e ≠ f := fun hh => he (hh ▸ hf)
        exact Finset.disjoint_left.mp
          (hP (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hf) hne) hv hvf
      exact insert_exposed_edge_crosses hsmall hQ hC hx

/-- An actual union of two matchings admits a two-coloring, without an
assumed path decomposition or even-cycle certificate. -/
theorem matching_union_colorable (P Q : Graph V) (hP : Matching P) (hQ : Matching Q) :
    (simpleGraph (P ∪ Q)).Colorable 2 := by
  obtain ⟨C,hC⟩ := matching_union_exists_crosses P Q hP hQ
  exact crosses_colorable hC

end RobustMatching.R7GraphInterpretation

set_option pp.fullNames true
#print axioms RobustMatching.R7GraphInterpretation.matching_union_colorable
