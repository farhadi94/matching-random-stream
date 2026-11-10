import RandomOrderMatching.Algebra.Tutte.Padding
import RandomOrderMatching.Graph.EvenFactor.Weights

/-!
Exact finite assembly between the actual Tutte availability envelope and
partial-permutation witnesses; no assumed envelope representation is used.
-/
noncomputable section
open scoped BigOperators
open Equiv Finset

namespace RandomOrderMatching.Algebra.Tutte.Representation
open RandomOrderMatching.Algebra RandomOrderMatching.Algebra.Tutte
open RandomOrderMatching.Graph.EvenFactor
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem matching_arcs_completion (F : Finset (V × V))
    (hF : RandomOrderMatching.Graph.BipartiteDual.IsMatching F) :
    ∃ π : Equiv.Perm V, partialArcs (sourceSupport F) π = F := by
  classical
  have hleft : Function.Injective (fun e : F => e.val.1) := by
    intro e f he
    exact Subtype.ext (hF.1 e.property f.property he)
  have hright : Function.Injective (fun e : F => e.val.2) := by
    intro e f he
    exact Subtype.ext (hF.2 e.property f.property he)
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun e : F => e.val.1) (fun e : F => e.val.2) hleft hright
  refine ⟨π,?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hi
    have hh := hπ ⟨e,he⟩
    have heq : (i,π i) = e := Prod.ext hei.symm (by simpa [hei] using hh)
    exact heq.symm ▸ he
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨p.1,Finset.mem_image_of_mem Prod.fst hp,?_⟩
    exact Prod.ext rfl (hπ ⟨p,hp⟩)

theorem partialArcs_weight_sum (w : Sym2 V → ℕ) (I : Finset V) (π : Equiv.Perm V) :
    (∑ p ∈ partialArcs I π, w s(p.1,p.2)) = ∑ i ∈ I, w s(i,π i) := by
  unfold partialArcs
  rw [Finset.sum_image (fun i _ j _ h => congrArg Prod.fst h)]

theorem available_basis_nonempty (G : SimpleGraph V) (w : Sym2 V → ℕ) (R : Finset V) :
    (columnBases (augmentedTutte G w) (identityColumns ∪ originalColumns R)).Nonempty := by
  apply columnBases_nonempty _ _ _ Sum.inr
  · rw [identity_basis,Matrix.det_one]
    exact one_ne_zero
  · intro i
    simp [identityColumns]

/-- Arbitrary original-column availability is retained by the actual upper witness. -/
theorem availableTutte_upper_witness (G : SimpleGraph V) (w : Sym2 V → ℕ) (R : Finset V) :
    ∃ (I : Finset V) (π : Equiv.Perm V),
      (∀ i ∈ I, G.Adj i (π i)) ∧
      (∀ i ∈ I, π i ∈ R) ∧
      (∀ c ∈ π.cycleFactorsFinset, c.support ⊆ I → Even c.support.card) ∧
      availableTutteValue G w R ≤ ∑ i ∈ I, (w s(i,π i) : ℤ) := by
  obtain ⟨b,hb,hval⟩ := columnEnvelope_attained (augmentedTutte G w)
    (identityColumns ∪ originalColumns R) (available_basis_nonempty G w R)
  obtain ⟨hbn,hbavail⟩ := (mem_columnBases _ _ b).mp hb
  obtain ⟨ρ,I,hn,hd,hcols⟩ := column_tuple_completed_minor (weightedTutte G w) b hbn
  obtain ⟨π,hcomp,hG,hcycles,hupper⟩ := weighted_completed_upper_witness I G w ρ hn
  refine ⟨I,π,hG,?_,hcycles,?_⟩
  · intro i hi
    obtain ⟨k,hk,hki⟩ := Finset.mem_image.mp (completion_image_mem I ρ π hcomp hi)
    obtain ⟨j,hj⟩ := hcols k hk
    have hh := hbavail j
    rw [hj,hki] at hh
    simpa [identityColumns,originalColumns] using hh
  · rw [hd] at hupper
    simpa only [availableTutteValue] using hval.symm ▸ hupper

/-- Any actual completed minor whose selected target columns are available
provides a lower bound on the actual envelope. -/
theorem completed_minor_le_available (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (R I : Finset V) (π : Equiv.Perm V)
    (hn : (completedMatrix I (weightedTutte G w) π).det ≠ 0)
    (havail : ∀ i ∈ I, π i ∈ R) :
    (completedMatrix I (weightedTutte G w) π).det.intDegree ≤ availableTutteValue G w R := by
  obtain ⟨hb,hval⟩ := completed_minor_padded_tuple I (weightedTutte G w) π hn
  have hmem : paddedColumns I π ∈ columnBases (augmentedTutte G w)
      (identityColumns ∪ originalColumns R) := by
    apply (mem_columnBases _ _ _).mpr
    refine ⟨hb,?_⟩
    intro i
    by_cases hi : i ∈ I
    · simp [paddedColumns,hi,identityColumns,originalColumns,havail i hi]
    · simp [paddedColumns,hi,identityColumns,originalColumns]
  have hu := columnEnvelope_upper _ _ _ hmem
  change ((augment (weightedTutte G w)).submatrix id (paddedColumns I π)).det.intDegree ≤
    availableTutteValue G w R at hu
  rwa [hval] at hu

end RandomOrderMatching.Algebra.Tutte.Representation
