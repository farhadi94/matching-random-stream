import RandomOrderMatching.Analysis.FixedHost.GraphCertificate
import RandomOrderMatching.Analysis.FixedHost.SuffixChronology
import RandomOrderMatching.Phases.Embedding.RepairWitnesses
import RandomOrderMatching.Phases.Execution.RepairComparison

/-! Actual original-edge phase-bank comparison on the physical cutoff
bracket. Both copied embeddings are constructed from graph/parent facts. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
open Classical
open scoped BigOperators
namespace RandomOrderMatching.Analysis.FixedHost
open RandomOrderMatching.Graph RandomOrderMatching.Analysis.Profile RandomOrderMatching.Analysis.Repair.Labeling RandomOrderMatching.Analysis.Repair.Probability
open RandomOrderMatching.Analysis.Repair.Typed RandomOrderMatching.Probability.ClockCoupling RandomOrderMatching.Phases.Execution RandomOrderMatching.Phases.Embedding
open RandomOrderMatching.Graph.BipartiteExchange
variable {V B : Type*} [Fintype V] [LinearOrder V] [Fintype B]

theorem crosses_originalSides {W : ℕ} (H : Graph (V×Fin W)) (cut : Finset V)
    (hc : Crosses H (copyCut cut W)) :
    ∀u v,(RandomOrderMatching.Graph.Konig.simpleGraph H).Adj u v → originalSide cut u.1≠originalSide cut v.1 := by
  intro u v huv
  obtain ⟨⟨e,he,hev⟩,hne⟩ := huv
  have hp : e.val={u,v} := by simpa only [Sym2.toFinset_mk_eq] using hev.symm
  have hs := RandomOrderMatching.Graph.EvenFactor.crossing_edge_sides hc he
    (show u∈e.val by rw [hp]; simp) (show v∈e.val by rw [hp]; simp) hne
  simp only [copyCut,Finset.mem_filter,Finset.mem_univ,true_and] at hs
  by_cases hu : u.1∈cut
  · have hv := hs.mp hu
    simp [originalSide,hu,hv]
  · have hv : v.1∈cut := by by_contra hv; exact hu (hs.mpr hv)
    simp [originalSide,hu,hv]

def outputValue (w : Edge V→ℕ) (H0 : Graph V) (eligible : Edge V→Prop)
    (stream : List (Edge V)) (cuts : Finset ℕ) : ℝ :=
  ∑e∈outputMatching w H0 eligible stream cuts,(w e:ℝ)

variable (W : ℕ) (MC H A : Graph (V×Fin W)) (hMC : Matching MC)
  (C : Finset (V×Fin W)) (beta : ℝ)
local notation "bin" => actualDegreeBin H beta
local notation "mask" => actualMinimumMask MC hMC C A bin H beta
local notation "d" => canonicalCoordinates MC H hMC C A beta
local notation "rawD" => coordinatesFromMatching MC hMC C A bin mask
local instance : DecidableEq (CanonicalCenters rawD) := Classical.decEq _
local instance : DecidableEq (CanonicalOutsides rawD) := Classical.decEq _
local instance : DecidableEq (CanonicalVertex rawD) := Classical.decEq _

include MC H hMC beta in
theorem actual_base_le_output {n : ℕ} (original : B→Edge V) (e : Fin n≃B)
    (w : Edge V→ℕ) (parent : Edge (V×Fin W)→Edge V)
    (H0 : Graph V) (eligible : Edge V→Prop) (cut : Finset V)
    (hAcross : Crosses A (copyCut cut W)) (hAcopies : ConsistentCopies W w parent A)
    (hav : ∀f∈A,parent f∈H0 ∨ (eligible (parent f) ∧ ∃b,original b=parent f))
    (hminimum : rank A=C.card) (σ : Equiv.Perm (Fin n)) :
    (C.card:ℝ)≤outputValue w H0 eligible (suffixStream original e σ) (RandomOrderMatching.Streaming.reachedCuts n) := by
  have ha : ∀f∈A,parent f∈H0 ∨ (eligible (parent f) ∧ parent f∈suffixStream original e σ) := by
    intro f hf
    rcases hav f hf with hh|⟨hel,b,hb⟩
    · exact Or.inl hh
    · exact Or.inr ⟨hel,hb ▸ suffixStream_mem original e σ b⟩
  let Qb := canonicalBaseEmbedding W MC hMC C A bin mask w parent H0 eligible
    (suffixStream original e σ) (RandomOrderMatching.Streaming.reachedCuts n) cut hAcross hAcopies ha
  have hh := @CopiedBaseEmbedding.rank_le_output V (CanonicalVertex rawD) _ _
    (Classical.decEq _) _ _ _ _ _ _ Qb
  rw [canonicalTypedBase_rank,hminimum] at hh
  exact hh

theorem coupled_analytic_le_output {n : ℕ}
    (original : B→Edge V) (e : Fin n≃B) (par : MC→B) (b0 : B)
    (κ : ℕ) (hk : 0<κ) (hfiber : ∀b,Fintype.card {f:MC //par f=b}≤κ)
    (w : Edge V→ℕ) (parent : Edge (V×Fin W)→Edge V)
    (hpar : ∀f:MC,parent f.val=original (par f))
    (H0 : Graph V) (eligible : Edge V→Prop) (cut : Finset V)
    (hHcross : Crosses H (copyCut cut W)) (hAcross : Crosses A (copyCut cut W))
    (hMcross : Crosses MC (copyCut cut W))
    (hHcopies : ConsistentCopies W w parent H) (hAcopies : ConsistentCopies W w parent A)
    (hMcopies : ConsistentCopies W w parent MC)
    (href : ∀f∈H,parent f∈H0)
    (hav : ∀f∈A,parent f∈H0 ∨ (eligible (parent f) ∧ ∃b,original b=parent f))
    (hminimum : rank A=C.card)
    (hbeta : 0<beta) (hcover : ∀f∈H,∃v∈f.val,v∈C)
    (hupper : ∀f∈H,incidenceDegree H (orientedEndpoint C f 0)+
      incidenceDegree H (orientedEndpoint C f 1)≤beta)
    (hn : 10000000≤n) (s : (Fin n→Clock)×Equiv.Perm (Fin n))
    (hbracket : cutoffBracket (RandomOrderMatching.Streaming.selectedCutoff n) (coupledClocks s)) :
    let D := graphLocalData MC H hMC C A beta par b0 κ hk hfiber
      (fun x=>originalSide cut x.1) (crosses_originalSides H cut hHcross) hbeta hcover hupper
    analyticValue D (labeledClocks e s)≤
      outputValue w H0 eligible (suffixStream original e (coupledOrder s)) (RandomOrderMatching.Streaming.reachedCuts n) := by
  dsimp only
  let D := graphLocalData MC H hMC C A beta par b0 κ hk hfiber
    (fun x=>originalSide cut x.1) (crosses_originalSides H cut hHcross) hbeta hcover hupper
  let stream := suffixStream original e (coupledOrder s)
  let cuts := RandomOrderMatching.Streaming.reachedCuts n
  let c := RandomOrderMatching.Streaming.selectedCutoff n
  have ha : ∀f∈A,parent f∈H0 ∨ (eligible (parent f) ∧ parent f∈stream) := by
    intro f hf
    rcases hav f hf with hh|⟨hel,b,hb⟩
    · exact Or.inl hh
    · exact Or.inr ⟨hel,hb ▸ suffixStream_mem original e (coupledOrder s) b⟩
  have ht := coupled_physical_chronology original e s c hbracket
  let Q := canonicalPhaseEmbedding W MC hMC C A bin mask w parent original par hpar
    H0 eligible stream cuts cut (labeledClocks e s) H c c c
    (selected_phase_active hn original e (coupledOrder s)) le_rfl le_rfl
    hHcross hMcross hHcopies hMcopies href ha ht.1 ht.2
  let Qb := canonicalBaseEmbedding W MC hMC C A bin mask w parent H0 eligible stream cuts cut
    hAcross hAcopies ha
  have hb := @CopiedBaseEmbedding.rank_le_output V (CanonicalVertex rawD) _ _
    (Classical.decEq _) _ _ _ _ _ _ Qb
  rw [canonicalTypedBase_rank,hminimum] at hb
  apply analyticValue_le D
  · have hcard : Fintype.card (CanonicalCenters d)=C.card := actual_center_card MC hMC C A bin mask
    change (Fintype.card (CanonicalCenters d):ℝ)≤_
    rw [hcard]
    exact hb
  · apply typed_transfer_from_execution w H0 eligible stream cuts
      (states D.parents (labeledClocks e s)) D.H D.sideC D.sideO
    convert Q using 1
    congr 1
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
      | (congr 1; all_goals first | rfl | exact Subsingleton.elim _ _)
      | (funext v; cases v <;> rfl)

end RandomOrderMatching.Analysis.FixedHost
