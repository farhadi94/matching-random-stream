import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-!
Actual general-graph matchings, with edges represented as two-element vertex
finsets. No bipartiteness restriction is built into `Graph` or `Matching`.
-/
noncomputable section
set_option linter.unusedSectionVars false
namespace RandomOrderMatching.Graph

variable {V : Type*} [DecidableEq V]

abbrev Edge (V : Type*) [DecidableEq V] := {s : Finset V // s.card = 2}
abbrev Graph (V : Type*) [DecidableEq V] := Finset (Edge V)

def Matching (M : Graph V) : Prop :=
  (M : Set (Edge V)).PairwiseDisjoint Subtype.val

instance (M : Graph V) : Decidable (Matching M) := Classical.propDecidable _

def covered (M : Graph V) : Finset V := M.biUnion Subtype.val

@[simp] theorem mem_covered {v : V} {M : Graph V} :
    v ∈ covered M ↔ ∃ e ∈ M, v ∈ e.val := by
  simp [covered]

theorem covered_mono {M N : Graph V} (h : M ⊆ N) : covered M ⊆ covered N := by
  intro v hv
  obtain ⟨e, he, hv⟩ := mem_covered.mp hv
  exact mem_covered.mpr ⟨e, h he, hv⟩

@[simp] theorem covered_union (M N : Graph V) :
    covered (M ∪ N) = covered M ∪ covered N := by
  ext v
  simp only [mem_covered, Finset.mem_union]
  aesop

theorem matching_mono {M N : Graph V} (hM : Matching M) (hNM : N ⊆ M) :
    Matching N := by
  intro e he f hf hne
  exact hM (hNM he) (hNM hf) hne

theorem covered_card {M : Graph V} (hM : Matching M) :
    (covered M).card = 2 * M.card := by
  rw [covered, Finset.card_biUnion hM]
  calc
    ∑ e ∈ M, e.val.card = ∑ _e ∈ M, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact e.property
    _ = 2 * M.card := by simp [Nat.mul_comm]

def rank (G : Graph V) : ℕ :=
  G.powerset.sup fun M => if Matching M then M.card else 0

theorem matching_card_le_rank {G M : Graph V} (hMG : M ⊆ G) (hM : Matching M) :
    M.card ≤ rank G := by
  simpa [rank, hM] using
    (Finset.le_sup (f := fun M : Graph V => if Matching M then M.card else 0)
      (Finset.mem_powerset.mpr hMG))

theorem rank_le {G : Graph V} {n : ℕ}
    (h : ∀ M ⊆ G, Matching M → M.card ≤ n) : rank G ≤ n := by
  apply Finset.sup_le
  intro M hM
  split_ifs with hm
  · exact h M (Finset.mem_powerset.mp hM) hm
  · exact Nat.zero_le _

theorem rank_mono {G H : Graph V} (hGH : G ⊆ H) : rank G ≤ rank H := by
  apply rank_le
  intro M hMG hM
  exact matching_card_le_rank (hMG.trans hGH) hM

theorem rank_attained (G : Graph V) :
    ∃ M ⊆ G, Matching M ∧ M.card = rank G := by
  let ms := G.powerset.filter Matching
  have hne : ms.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    simp [Matching]
  obtain ⟨M, hM, hmax⟩ := ms.exists_max_image Finset.card hne
  obtain ⟨hMG, hm⟩ := Finset.mem_filter.mp hM
  have hsub := Finset.mem_powerset.mp hMG
  refine ⟨M, hsub, hm, Nat.le_antisymm (matching_card_le_rank hsub hm) ?_⟩
  apply rank_le
  intro N hNG hn
  exact hmax N (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hNG, hn⟩)

theorem matching_insert {M : Graph V} {e : Edge V} (hM : Matching M)
    (hd : Disjoint e.val (covered M)) : Matching (insert e M) := by
  intro f hf g hg hfg
  rcases Finset.mem_insert.mp hf with rfl | hfM
  · rcases Finset.mem_insert.mp hg with rfl | hg
    · exact (hfg rfl).elim
    · exact hd.mono_right (fun v hv => mem_covered.mpr ⟨g, hg, hv⟩)
  · rcases Finset.mem_insert.mp hg with rfl | hg
    · have hfsub : f.val ⊆ covered M := by
        intro v hv
        exact mem_covered.mpr ⟨f, hfM, hv⟩
      exact (hd.mono_right hfsub).symm
    · exact hM hfM hg hfg

/-- Singleton rank closure forces every maximum matching to meet the edge. -/
theorem closed_edge_meets_maximum {K P : Graph V} {e : Edge V}
    (hPK : P ⊆ K) (hP : Matching P) (hPc : P.card = rank K)
    (hc : rank (insert e K) = rank K) :
    (e.val ∩ covered P).Nonempty := by
  by_contra hn
  have hd : Disjoint e.val (covered P) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.not_nonempty_iff_eq_empty.mp hn
  have he : e ∉ P := by
    intro he
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < e.val.card by rw [e.property]; decide)
    exact Finset.disjoint_left.mp hd hv (mem_covered.mpr ⟨e, he, hv⟩)
  have hsub : insert e P ⊆ insert e K := Finset.insert_subset_insert e hPK
  have hh := matching_card_le_rank hsub (matching_insert hP hd)
  rw [Finset.card_insert_of_notMem he, hc, ← hPc] at hh
  omega

/-- An actual matching has at most as many edges as any vertex set meeting all of them. -/
theorem matching_le_cover {J : Graph V} {S : Finset V} (hJ : Matching J)
    (hS : ∀ e ∈ J, (e.val ∩ S).Nonempty) : J.card ≤ S.card := by
  classical
  let chooseV : Edge V → V := fun e =>
    if he : e ∈ J then (hS e he).choose else Classical.choice (show Nonempty V from by
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < e.val.card by rw [e.property]; decide)
      exact ⟨v⟩)
  have hmem (e : Edge V) (he : e ∈ J) : chooseV e ∈ e.val ∩ S := by
    simp only [chooseV, dif_pos he]
    exact (hS e he).choose_spec
  have hinj : Set.InjOn chooseV (J : Set (Edge V)) := by
    intro e he f hf hef
    by_contra hne
    have hd := hJ he hf hne
    exact Finset.disjoint_left.mp hd (Finset.mem_inter.mp (hmem e he)).1
      (hef ▸ (Finset.mem_inter.mp (hmem f hf)).1)
  have hsub : J.image chooseV ⊆ S := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_inter.mp (hmem e he)).2
  rw [← Finset.card_image_iff.mpr hinj]
  exact Finset.card_le_card hsub

theorem rank_insert_le (G : Graph V) (e : Edge V) :
    rank (insert e G) ≤ rank G + 1 := by
  apply rank_le
  intro M hM hm
  have herase : M.erase e ⊆ G := by
    intro f hf
    have hfM := (Finset.mem_erase.mp hf).2
    rcases Finset.mem_insert.mp (hM hfM) with h | h
    · exact ((Finset.mem_erase.mp hf).1 h).elim
    · exact h
  have hc := matching_card_le_rank herase (matching_mono hm (Finset.erase_subset e M))
  have hcard : M.card ≤ (M.erase e).card + 1 := by
    by_cases he : e ∈ M
    · rw [Finset.card_erase_of_mem he]
      have := Finset.card_pos.mpr ⟨e, he⟩
      omega
    · simp [Finset.erase_eq_of_notMem he]
  omega

theorem rank_insert_of_lt {G : Graph V} {e : Edge V}
    (h : rank G < rank (insert e G)) : rank (insert e G) = rank G + 1 := by
  have := rank_insert_le G e
  omega

/-- An already rejected edge remains rejected after every accepted edge. -/
theorem rejected_persists_one {G : Graph V} {e f : Edge V}
    (he : rank (insert e G) = rank G)
    (hf : rank G < rank (insert f G)) :
    rank (insert e (insert f G)) = rank (insert f G) := by
  apply Nat.le_antisymm
  · have hu := rank_insert_le (insert e G) f
    rw [Finset.insert_comm, he, ← rank_insert_of_lt hf] at hu
    exact hu
  · exact rank_mono (Finset.subset_insert _ _)

def retain (G : Graph V) (e : Edge V) : Graph V :=
  if rank G < rank (insert e G) then insert e G else G

def phase (G : Graph V) (es : List (Edge V)) : Graph V :=
  es.foldl retain G

theorem subset_retain (G : Graph V) (e : Edge V) : G ⊆ retain G e := by
  unfold retain
  split_ifs
  · exact Finset.subset_insert _ _
  · rfl

theorem rejected_persists_retain {G : Graph V} {e f : Edge V}
    (he : rank (insert e G) = rank G) :
    rank (insert e (retain G f)) = rank (retain G f) := by
  unfold retain
  split_ifs with hf
  · exact rejected_persists_one he hf
  · exact he

theorem processed_closed (G : Graph V) (e : Edge V) :
    rank (insert e (retain G e)) = rank (retain G e) := by
  unfold retain
  split_ifs with h
  · simp
  · exact Nat.le_antisymm (Nat.le_of_not_gt h)
      (rank_mono (Finset.subset_insert e G))

theorem rejected_persists_phase (G : Graph V) (es : List (Edge V))
    (e : Edge V) (he : rank (insert e G) = rank G) :
    rank (insert e (phase G es)) = rank (phase G es) := by
  induction es generalizing G with
  | nil => exact he
  | cons f es ih => exact ih (retain G f) (rejected_persists_retain he)

/-- The actual retained graph is singleton-closed against every processed edge. -/
theorem phase_closed (G : Graph V) (es : List (Edge V))
    (e : Edge V) (he : e ∈ es) :
    rank (insert e (phase G es)) = rank (phase G es) := by
  induction es generalizing G with
  | nil => simp at he
  | cons f es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact rejected_persists_phase (retain G e) es e (processed_closed G e)
    · exact ih (retain G f) he

/-- Exact rank accounting for additional retained edge records. -/
theorem retain_card_rank (G : Graph V) (e : Edge V) :
    (retain G e).card + rank G = G.card + rank (retain G e) := by
  unfold retain
  split_ifs with h
  · have he : e ∉ G := by
      intro he
      simp [Finset.insert_eq_of_mem he] at h
    rw [Finset.card_insert_of_notMem he, rank_insert_of_lt h]
    omega
  · rfl

theorem phase_card_rank (G : Graph V) (es : List (Edge V)) :
    (phase G es).card + rank G = G.card + rank (phase G es) := by
  induction es generalizing G with
  | nil => rfl
  | cons e es ih =>
    have hi := ih (retain G e)
    have hr := retain_card_rank G e
    change (phase (retain G e) es).card + rank G =
      G.card + rank (phase (retain G e) es)
    omega


end RandomOrderMatching.Graph
#print axioms RandomOrderMatching.Graph.closed_edge_meets_maximum
#print axioms RandomOrderMatching.Graph.matching_le_cover
