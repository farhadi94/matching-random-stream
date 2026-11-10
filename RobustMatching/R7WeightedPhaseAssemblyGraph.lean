import RobustMatching.R7WeightedPhaseAssemblyCopies
import RobustMatching.R7WeightedPhaseAssemblyRelabel

/-! Graph-rank forms of the concrete copied phase theorem. Typed repairs
may use arbitrary finite vertex labels; an injective actual copy labeling
transports their matchings and deletion ranks without a rank premise. -/
noncomputable section
open scoped BigOperators
namespace RobustMatching.R7WeightedPhaseAssembly
open RobustMatching.R2Cut RobustMatching.R7WeightedPhase RobustMatching.R6FableImportance
open RobustMatching.Dual RobustMatching.R6FableSharpDualCopy
open RobustMatching.R7CopyDualGeneralBridge
variable {V T : Type*} [Fintype V] [LinearOrder V] [DecidableEq T]

/-- Native encoding of the actual two endpoint-deleted source graphs
suffices for the historical transfer bound on their actual ranks. -/
theorem bank_relabelled_copy_transfer
    (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) (a c t : ℕ)
    (hc : c ∈ activeCuts cuts stream) (hac : a ≤ c) (hct : c ≤ t)
    (cut : Finset V) (W : ℕ) (E P : Finset (Left cut × Right cut))
    (hE : encode cut E ⊆ initial H eligible stream a)
    (hP : ∀ e ∈ encode cut P, e ∈ sharedBase H eligible stream ∨ e ∈ stream.drop t)
    (B S : Finset ((Left cut × Fin W) × (Right cut × Fin W)))
    (hB : ∀ e ∈ B, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p)))
    (hsub : ∀ e ∈ S, R7CopyDual.parent e ∈ P)
    (hidx : ∀ e ∈ S, e.1.2.val+e.2.2.val+1=w (edgeOf cut (R7CopyDual.parent e)))
    (f : T → (Left cut × Fin W) ⊕ (Right cut × Fin W)) (hf : Function.Injective f)
    (D1 D2 J : Graph T) (hJ : Matching J)
    (hJS : mapGraph f hf J = R7GraphDualBridge.encode S)
    (hD1 : mapGraph f hf D1 ⊆
      R7GraphDualBridge.encode (B.filter (fun e => e.1 ∉ S.image Prod.fst)))
    (hD2 : mapGraph f hf D2 ⊆
      R7GraphDualBridge.encode (B.filter (fun e => e.2 ∉ S.image Prod.snd))) :
    (rank D1 : ℝ)+rank D2+J.card ≤
      2 * ∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ) := by
  classical
  obtain ⟨C1,hC1,hc1,hr1⟩ := rank_matching_into_pairs f hf D1 _ hD1
  obtain ⟨C2,hC2,hc2,hr2⟩ := rank_matching_into_pairs f hf D2 _ hD2
  have hS : IsMatching S := R7GraphDualBridge.encode_matching_iff S |>.mp
    (hJS ▸ (mapGraph_matching_iff f hf J).mpr hJ)
  have hc : S.card = J.card := by
    have hh := congrArg Finset.card hJS
    rw [mapGraph_card,R7GraphDualBridge.encode_card] at hh
    exact hh.symm
  have hd1 : Disjoint (C1.image Prod.fst) (S.image Prod.fst) := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp (hC1 he)).2 hs
  have hd2 : Disjoint (C2.image Prod.snd) (S.image Prod.snd) := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp (hC2 he)).2 hs
  have hh := bank_copied_bound w H eligible stream cuts a c t ‹c ∈ activeCuts cuts stream›
    hac hct cut W E P hE hP C1 C2 S hc1 hc2 hS
    (fun e he => hB e (Finset.mem_filter.mp (hC1 he)).1)
    (fun e he => hB e (Finset.mem_filter.mp (hC2 he)).1) hsub hd1 hd2 hidx
  rwa [hr1,hr2,hc] at hh

/-- Base-rank domination is proved by actual copied matching extraction
and bipartite refolding into the complete shared original base. -/
theorem bank_relabelled_base_bound
    (w : Edge V → ℕ) (H : Graph V) (eligible : Edge V → Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ)
    (cut : Finset V) (W : ℕ) (E : Finset (Left cut × Right cut))
    (hE : encode cut E ⊆ sharedBase H eligible stream)
    (B : Finset ((Left cut × Fin W) × (Right cut × Fin W)))
    (hB : ∀ e ∈ B, e ∈ CopyEdges W (E : Set _) (fun p => w (edgeOf cut p)))
    (f : T → (Left cut × Fin W) ⊕ (Right cut × Fin W)) (hf : Function.Injective f)
    (G : Graph T) (hG : mapGraph f hf G ⊆ R7GraphDualBridge.encode B) :
    (rank G : ℝ) ≤ ∑ e ∈ outputMatching w H eligible stream cuts, (w e : ℝ) := by
  obtain ⟨C,hC,hm,hcard⟩ := rank_matching_into_pairs f hf G B hG
  have hh := bank_base_copy_bound w H eligible stream cuts cut W E hE C hm
    (fun e he => hB e (hC he))
  rwa [hcard] at hh

end RobustMatching.R7WeightedPhaseAssembly
#print axioms RobustMatching.R7WeightedPhaseAssembly.bank_relabelled_copy_transfer
#print axioms RobustMatching.R7WeightedPhaseAssembly.bank_relabelled_base_bound
