import RandomOrderMatching.Graph.Basic
import RandomOrderMatching.Packing.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Graph.WeightedMatching
open RandomOrderMatching.Graph RandomOrderMatching.Packing
variable {V : Type*} [DecidableEq V]

theorem empty_matching : Matching (∅ : Graph V) := by simp [Matching]

def opt (w : Edge V → ℝ) (G : Graph V) : ℝ :=
  packingOpt Matching empty_matching w G

def avoid (G : Graph V) (e : Edge V) : Graph V := by
  classical
  exact G.filter (fun f => Disjoint f.val e.val)

theorem avoid_subset (G : Graph V) (e : Edge V) : avoid G e ⊆ G :=
  Finset.filter_subset _ _

theorem avoid_excludes (G : Graph V) (e : Edge V) : e ∉ avoid G e := by
  classical
  intro he
  have hd := (Finset.mem_filter.mp he).2
  have hp : 0 < e.val.card := by rw [e.property]; norm_num
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hp
  exact Finset.disjoint_left.mp hd hv hv

theorem matching_erase_avoids (G M : Graph V) (e : Edge V)
    (hM : Matching M) (he : e ∈ M) (hMG : M ⊆ insert e G) :
    M.erase e ⊆ avoid G e := by
  classical
  intro f hf
  obtain ⟨hne,hfM⟩ := Finset.mem_erase.mp hf
  apply Finset.mem_filter.mpr
  constructor
  · exact (Finset.mem_insert.mp (hMG hfM)).resolve_left hne
  · exact hM hfM he hne

theorem avoid_matching_insert (G N : Graph V) (e : Edge V)
    (hN : Matching N) (hNG : N ⊆ avoid G e) : Matching (insert e N) := by
  classical
  apply matching_insert hN
  apply Finset.disjoint_left.mpr
  intro v hv hvN
  obtain ⟨f,hf,hvf⟩ := mem_covered.mp hvN
  have hd := (Finset.mem_filter.mp (hNG hf)).2
  exact Finset.disjoint_left.mp hd hvf hv

/-- Exact weighted insertion formula on an actual general graph. -/
theorem opt_insert (w : Edge V → ℝ) (G : Graph V) (e : Edge V) :
    opt w (insert e G) = max (opt w G) (w e + opt w (avoid G e)) := by
  classical
  apply le_antisymm
  · obtain ⟨M,hMG,hM,hval⟩ := packingOpt_attained Matching empty_matching w (insert e G)
    change packingOpt Matching empty_matching w (insert e G) ≤ _
    rw [hval]
    by_cases he : e ∈ M
    · have hb := weight_le_packingOpt Matching empty_matching w
        (matching_mono hM (Finset.erase_subset e M))
        (matching_erase_avoids G M e hM he hMG)
      have hs := Finset.sum_erase_add M w he
      change (∑ x ∈ M.erase e, w x) ≤ opt w (avoid G e) at hb
      exact (by linarith : (∑ x ∈ M, w x) ≤ w e + opt w (avoid G e)).trans (le_max_right _ _)
    · have hsub : M ⊆ G := by
        intro f hf
        rcases Finset.mem_insert.mp (hMG hf) with h | h
        · exact False.elim (he (h ▸ hf))
        · exact h
      exact (weight_le_packingOpt Matching empty_matching w hM hsub).trans (le_max_left _ _)
  · apply max_le
    · exact packingOpt_mono Matching empty_matching w (Finset.subset_insert e G)
    · obtain ⟨N,hNG,hN,hval⟩ := packingOpt_attained Matching empty_matching w (avoid G e)
      have heN : e ∉ N := fun h => avoid_excludes G e (hNG h)
      have hi := weight_le_packingOpt Matching empty_matching w
        (avoid_matching_insert G N e hN hNG)
        (Finset.insert_subset_insert e (hNG.trans (avoid_subset G e)))
      rw [Finset.sum_insert heN] at hi
      change w e + (∑ f ∈ N, w f) ≤ opt w (insert e G) at hi
      simpa only [opt, hval] using hi

def price (w : Edge V → ℝ) (G : Graph V) (e : Edge V) : ℝ :=
  opt w G - opt w (avoid G e)

theorem price_nonneg (w : Edge V → ℝ) (G : Graph V) (e : Edge V) :
    0 ≤ price w G e := sub_nonneg.mpr
      (packingOpt_mono Matching empty_matching w (avoid_subset G e))

theorem insertion_gain (w : Edge V → ℝ) (G : Graph V) (e : Edge V) :
    opt w (insert e G) - opt w G = max 0 (w e - price w G e) := by
  rw [opt_insert]
  unfold price
  by_cases h : w e + opt w (avoid G e) ≤ opt w G
  · rw [max_eq_left h, max_eq_left (by linarith)]
    ring
  · have h' : opt w G ≤ w e + opt w (avoid G e) := le_of_not_ge h
    rw [max_eq_right h', max_eq_right (by linarith)]
    ring

/-- The proposed deletion-price test is exactly the incremental optimum test. -/
theorem acceptance_equiv (w : Edge V → ℝ) (G : Graph V) (e : Edge V)
    (θ : ℝ) (hw : 0 < w e) (hθ : θ < 1) :
    (1-θ)*w e ≤ opt w (insert e G)-opt w G ↔ price w G e ≤ θ*w e := by
  rw [insertion_gain]
  have hp : 0 < (1-θ)*w e := mul_pos (by linarith) hw
  constructor
  · intro h
    by_cases hn : w e-price w G e ≤ 0
    · rw [max_eq_left hn] at h
      linarith
    · rw [max_eq_right (le_of_not_ge hn)] at h
      nlinarith
  · intro h
    have hl : (1-θ)*w e ≤ w e-price w G e := by nlinarith
    exact hl.trans (le_max_right _ _)

end RandomOrderMatching.Graph.WeightedMatching

#print axioms RandomOrderMatching.Graph.WeightedMatching.opt_insert
#print axioms RandomOrderMatching.Graph.WeightedMatching.acceptance_equiv
