import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators
namespace RobustMatching.R1Kernel

/-- An edge is represented by its two-element vertex set. -/
def IsMatching {V : Type*} [DecidableEq V] (M : Finset (Finset V)) : Prop :=
  (∀ e ∈ M, e.card = 2) ∧
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

def occupied {V : Type*} [DecidableEq V] (M : Finset (Finset V)) : Finset V :=
  M.biUnion id

lemma occupied_card_le {V : Type*} [DecidableEq V]
    (M : Finset (Finset V)) (hM : IsMatching M) :
    (occupied M).card ≤ 2 * M.card := by
  calc
    _ ≤ ∑ e ∈ M, e.card := Finset.card_biUnion_le
    _ = ∑ _e ∈ M, 2 := Finset.sum_congr rfl (fun e he => hM.1 e he)
    _ = 2 * M.card := by simp [mul_comm]

lemma matching_erase {V : Type*} [DecidableEq V]
    {M : Finset (Finset V)} (hM : IsMatching M) (e : Finset V) :
    IsMatching (M.erase e) := by
  constructor
  · intro f hf
    exact hM.1 f (Finset.mem_of_mem_erase hf)
  · intro f hf g hg hfg
    exact hM.2 f (Finset.mem_of_mem_erase hf) g (Finset.mem_of_mem_erase hg) hfg

lemma free_pair_disjoint {V : Type*} [DecidableEq V]
    {M : Finset (Finset V)} {u z : V}
    (hu : u ∉ occupied M) (hz : z ∉ occupied M) {e : Finset V} (he : e ∈ M) :
    Disjoint ({u,z} : Finset V) e := by
  rw [Finset.disjoint_left]
  intro a ha hae
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact hu (Finset.mem_biUnion.mpr ⟨e, he, hae⟩)
  · exact hz (Finset.mem_biUnion.mpr ⟨e, he, hae⟩)

lemma free_pair_not_mem {V : Type*} [DecidableEq V]
    {M : Finset (Finset V)} {u z : V} (hu : u ∉ occupied M) :
    ({u,z} : Finset V) ∉ M := by
  intro he
  exact hu (Finset.mem_biUnion.mpr ⟨{u,z}, he, by simp⟩)

lemma matching_insert_free_pair {V : Type*} [DecidableEq V]
    {M : Finset (Finset V)} (hM : IsMatching M) {u z : V}
    (huz : u ≠ z) (hu : u ∉ occupied M) (hz : z ∉ occupied M) :
    IsMatching (insert ({u,z} : Finset V) M) := by
  constructor
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.card_pair huz
    · exact hM.1 e he
  · intro e he f hf hef
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim (hef rfl)
      · exact free_pair_disjoint hu hz hf
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact (free_pair_disjoint hu hz he).symm
      · exact hM.2 e he f hf hef

/-- The removed edge frees its covered endpoint. -/
lemma endpoint_free_after_erase {V : Type*} [DecidableEq V]
    {M : Finset (Finset V)} (hM : IsMatching M) {e : Finset V} (he : e ∈ M)
    {u : V} (hu : u ∈ e) : u ∉ occupied (M.erase e) := by
  intro h
  obtain ⟨f, hf, huf⟩ := Finset.mem_biUnion.mp h
  have hfe := Finset.mem_erase.mp hf
  exact (Finset.disjoint_left.mp (hM.2 e he f hfe.2 hfe.1.symm)) hu huf

/-- Sharp pigeonhole/exchange step: 2t-1 retained neighbors suffice after removing one
edge of a matching of size at most t. It preserves weight against any completion. -/
theorem retained_neighbor_exchange {V : Type*} [DecidableEq V]
    {M : Finset (Finset V)} (hM : IsMatching M) {t : ℕ} (ht : 1 ≤ t)
    (hsize : M.card ≤ t) {e : Finset V} (he : e ∈ M) {u : V} (hu : u ∈ e)
    (N : Finset V) (hN : 2*t-1 ≤ N.card) (hNu : u ∉ N)
    (w : Finset V → ℝ) (hw : ∀ z ∈ N, w e ≤ w {u,z}) :
    ∃ z ∈ N, let M' := insert ({u,z} : Finset V) (M.erase e)
      IsMatching M' ∧ M'.card = M.card ∧
      (∑ f ∈ M, w f) ≤ ∑ f ∈ M', w f := by
  have hcard := Finset.card_erase_add_one he
  have hocc := occupied_card_le (M.erase e) (matching_erase hM e)
  have hlt : (occupied (M.erase e)).card < N.card := by omega
  obtain ⟨z, hzN, hzfree⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hufree := endpoint_free_after_erase hM he hu
  have huz : u ≠ z := by intro h; subst z; exact hNu hzN
  have hnew : ({u,z} : Finset V) ∉ M.erase e := free_pair_not_mem hufree
  refine ⟨z, hzN, matching_insert_free_pair (matching_erase hM e) huz hufree hzfree, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnew]
    exact hcard
  · rw [Finset.sum_insert hnew]
    have hsum := Finset.sum_erase_add M w he
    have hweight := hw z hzN
    linarith

/-- A retained-list certificate is supplied by a vertex cover and its heaviest adjacency
lists. The finite exchange theorem does not assume that the target matching exists. -/
def RetainedLists {V : Type*} [DecidableEq V]
    (A K : Finset (Finset V)) (t : ℕ) (w : Finset V → ℝ) : Prop :=
  ∀ e ∈ A, e ∉ K → ∃ u ∈ e, ∃ N : Finset V,
    2*t-1 ≤ N.card ∧ u ∉ N ∧ ∀ z ∈ N, {u,z} ∈ K ∧ w e ≤ w {u,z}

/-- Full arbitrary-completion kernel preservation, from concrete retained adjacency lists.
The matching may be weighted and the graph need not be bipartite. -/
theorem completion_kernel_preserves {V : Type*} [DecidableEq V]
    (A B K : Finset (Finset V)) (t : ℕ) (ht : 1 ≤ t)
    (w : Finset V → ℝ) (hKA : K ⊆ A) (hlist : RetainedLists A K t w)
    (M : Finset (Finset V)) (hM : IsMatching M) (hsub : M ⊆ A ∪ B)
    (hsize : M.card ≤ t) :
    ∃ M', IsMatching M' ∧ M' ⊆ K ∪ B ∧ M'.card = M.card ∧
      (∑ e ∈ M, w e) ≤ ∑ e ∈ M', w e := by
  classical
  generalize hk : (M \ (K ∪ B)).card = k
  induction k using Nat.strong_induction_on generalizing M with
  | h k ih =>
    by_cases hzero : M \ (K ∪ B) = ∅
    · refine ⟨M, hM, ?_, rfl, le_rfl⟩
      exact Finset.sdiff_eq_empty_iff_subset.mp hzero
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
      have hem := (Finset.mem_sdiff.mp he).1
      have hekb := (Finset.mem_sdiff.mp he).2
      have heK : e ∉ K := by intro h; exact hekb (Finset.mem_union_left B h)
      have heB : e ∉ B := by intro h; exact hekb (Finset.mem_union_right K h)
      have heA : e ∈ A := (Finset.mem_union.mp (hsub hem)).resolve_right heB
      obtain ⟨u, hue, N, hN, hNu, hretain⟩ := hlist e heA heK
      obtain ⟨z, hz, hmatch, hcard, hweight⟩ := retained_neighbor_exchange hM ht hsize hem hue
        N hN hNu w (fun z hz => (hretain z hz).2)
      let M1 := insert ({u,z} : Finset V) (M.erase e)
      have hnewK : ({u,z} : Finset V) ∈ K := (hretain z hz).1
      have hnewKB : ({u,z} : Finset V) ∈ K ∪ B := Finset.mem_union_left B hnewK
      have hM1sub : M1 ⊆ A ∪ B ∪ K := by
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact Finset.mem_union_right _ hnewK
        · exact Finset.mem_union_left _ (hsub (Finset.mem_of_mem_erase hf))
      have hbad : M1 \ (K ∪ B) = (M \ (K ∪ B)).erase e := by
        dsimp [M1]
        rw [Finset.insert_sdiff_of_mem _ hnewKB, Finset.erase_sdiff_comm]
      have hsmaller : (M1 \ (K ∪ B)).card < k := by
        rw [hbad]
        have hc := Finset.card_erase_add_one he
        omega
      obtain ⟨M', hM', hsub', hcard', hw'⟩ := ih _ hsmaller M1 hmatch
        (fun f hf => by
          rcases Finset.mem_union.mp (hM1sub hf) with hf | hf
          · exact hf
          · exact Finset.mem_union_left B (hKA hf))
        (hcard.le.trans hsize) rfl
      exact ⟨M', hM', hsub', hcard'.trans hcard, hweight.trans hw'⟩

/-- Kernel edge union formed by one neighbor list at each cover vertex. -/
def listKernel {V : Type*} [DecidableEq V]
    (C : Finset V) (N : V → Finset V) : Finset (Finset V) :=
  C.biUnion (fun u => (N u).image (fun z => {u,z}))

/-- Direct word/edge count for the concrete kernel construction. -/
theorem listKernel_card_le {V : Type*} [DecidableEq V]
    (C : Finset V) (N : V → Finset V) (t : ℕ)
    (hC : C.card ≤ 2*t) (hN : ∀ u ∈ C, (N u).card ≤ 2*t-1) :
    (listKernel C N).card ≤ 2*t*(2*t-1) := by
  calc
    _ ≤ ∑ u ∈ C, ((N u).image (fun z => ({u,z} : Finset V))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ u ∈ C, (2*t-1) := Finset.sum_le_sum (fun u hu =>
      (Finset.card_image_le).trans (hN u hu))
    _ = C.card*(2*t-1) := by simp
    _ ≤ 2*t*(2*t-1) := Nat.mul_le_mul_right _ hC

/-- A cover and top-neighbor lists imply the retained-list certificate used in the
full completion theorem. The ranking assumption only compares weights of omitted edges. -/
theorem cover_lists_certificate {V : Type*} [DecidableEq V]
    (A : Finset (Finset V)) (C : Finset V) (N : V → Finset V)
    (t : ℕ) (w : Finset V → ℝ)
    (hcover : ∀ e ∈ A, ∃ u ∈ C, u ∈ e)
    (hloop : ∀ u ∈ C, u ∉ N u)
    (htop : ∀ e ∈ A, ∀ u ∈ C, u ∈ e → e ∉ listKernel C N →
      2*t-1 ≤ (N u).card ∧ ∀ z ∈ N u, w e ≤ w {u,z}) :
    RetainedLists A (listKernel C N) t w := by
  intro e he heK
  obtain ⟨u, huC, hue⟩ := hcover e he
  have hh := htop e he u huC hue heK
  refine ⟨u, hue, N u, hh.1, hloop u huC, ?_⟩
  intro z hz
  exact ⟨Finset.mem_biUnion.mpr ⟨u, huC, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩,
    hh.2 z hz⟩

#print axioms retained_neighbor_exchange
#print axioms completion_kernel_preserves
#print axioms listKernel_card_le
#print axioms cover_lists_certificate
end RobustMatching.R1Kernel
