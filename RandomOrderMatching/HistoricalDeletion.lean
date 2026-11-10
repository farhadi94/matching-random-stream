import RandomOrderMatching.Unfolding.PhaseTransfer

/-! Historical deletion for arbitrary disjoint vertex sets observed at arbitrary
times. The release order is constructed from the given observation times; no
ordered schedule, submodularity premise, or matching restriction is supplied.
Only the host prefix through the stated terminal time must be increasing. -/
noncomputable section
open Classical
open scoped BigOperators

namespace RandomOrderMatching.HistoricalDeletion
open RandomOrderMatching.Graph RandomOrderMatching.Graph.MarkedPair
open RandomOrderMatching.Graph.WeightedMatching RandomOrderMatching.HistoricalDeletion.Potential
open RandomOrderMatching.Algebra.Tutte.Representation

variable {V ι : Type*} [Fintype V] [LinearOrder V] [DecidableEq ι]

omit [Fintype V] in
private theorem union_erase_eq_difference (S : Finset ι) (X : ι → Finset V)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (X i) (X j))
    (i : ι) (hi : i ∈ S) :
    (S.erase i).biUnion X = S.biUnion X \ X i := by
  ext v
  constructor
  · intro hv
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨j, hjS, hvj⟩, ?_⟩
    intro hvi
    exact Finset.disjoint_left.mp (hd j hjS i hi hji) hvj hvi
  · intro hv
    obtain ⟨hvS, hvi⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvS
    have hji : j ≠ i := by
      intro he
      subst j
      exact hvi hvj
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, hvj⟩

/-- The current host may start at any time before all remaining observations.
Earliest-time induction constructs the legal release schedule. Empty demand
sets, an empty family, and equal observation times are all permitted. -/
theorem observed_deletion_budget
    (w : Edge V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (K : ℕ → Graph V) (m : ℕ)
    (hK : ∀ i j, i ≤ j → j ≤ m → K i ⊆ K j)
    (S : Finset ι) (X : ι → Finset V)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (X i) (X j))
    (time : ι → ℕ) (s : ℕ) (hs : s ≤ m)
    (hstart : ∀ i ∈ S, s ≤ time i)
    (hend : ∀ i ∈ S, time i ≤ m) :
    (∑ i ∈ S, (opt w (K (time i)) - opt w (deleteVertices (K (time i)) (X i)))) +
        pathValue w (K s) (S.biUnion X) ≤ 2 * opt w (K m) := by
  induction S using Finset.strongInductionOn generalizing s with
  | _ S ih =>
    by_cases hne : S.Nonempty
    · obtain ⟨i, hi, hmin⟩ := S.exists_min_image time hne
      have hd' : ∀ j ∈ S.erase i, ∀ k ∈ S.erase i, j ≠ k → Disjoint (X j) (X k) := by
        intro j hj k hk hjk
        exact hd j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk) hjk
      have hrest := ih (S.erase i) (Finset.erase_ssubset hi) hd' (time i) (hend i hi)
        (fun j hj => hmin j (Finset.mem_of_mem_erase hj))
        (fun j hj => hend j (Finset.mem_of_mem_erase hj))
      have hx : X i ⊆ S.biUnion X := by
        intro v hv
        exact Finset.mem_biUnion.mpr ⟨i, hi, hv⟩
      have hrelease := pathValue_release w (K (time i))
        (pathValue_submodular_real _ _ hw) (S.biUnion X) (X i) hx
      rw [← union_erase_eq_difference S X hd i hi] at hrelease
      have hhost := pathValue_host_mono w (hK s (time i) (hstart i hi) (hend i hi))
        (S.biUnion X)
      have hsum := Finset.sum_erase_add S
        (fun j => opt w (K (time j)) - opt w (deleteVertices (K (time j)) (X j))) hi
      linarith
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      have hhost := RandomOrderMatching.Packing.packingOpt_mono Matching empty_matching w
        (hK s m hs le_rfl)
      simp only [Finset.sum_empty, Finset.biUnion_empty, pathValue_empty, zero_add]
      change opt w (K s) ≤ opt w (K m) at hhost
      linarith

/-- The historical deletion inequality in the paper, with arbitrary finite
disjoint demand sets and arbitrary observation times in the host prefix.
All times, including zero and repeated times, are handled internally. -/
theorem historical_deletion_bound
    (w : Edge V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (K : ℕ → Graph V) (m : ℕ)
    (hK : ∀ i j, i ≤ j → j ≤ m → K i ⊆ K j)
    (S : Finset ι) (X : ι → Finset V)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (X i) (X j))
    (time : ι → ℕ) (ht : ∀ i ∈ S, time i ≤ m) :
    (∑ i ∈ S, (opt w (K (time i)) - opt w (deleteVertices (K (time i)) (X i)))) ≤
      2 * opt w (K m) - pathValue w (K 0) (S.biUnion X) := by
  have h := observed_deletion_budget w hw K m hK S X hd time 0 (Nat.zero_le _)
    (fun _ _ => Nat.zero_le _) ht
  linarith

end RandomOrderMatching.HistoricalDeletion
