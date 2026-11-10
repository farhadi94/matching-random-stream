import RandomOrderMatching.Phases.WeightedState
import RandomOrderMatching.Graph.Components

/-! The graph size implication used by the exact-prefix-buffer branch.
It is proved on actual simple general graphs and nonzero integer weights. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Acquisition.Probability
open RandomOrderMatching.Graph RandomOrderMatching.Phases.WeightedState
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem graph_card_le_cover (G : Graph V) (C : Finset V)
    (hC : ∀ e ∈ G, (e.val ∩ C).Nonempty) :
    G.card ≤ C.card * Fintype.card V := by
  have hp (e : G) : ∃ u v : V, u ∈ C ∧ u ≠ v ∧ e.val.val = {u,v} := by
    obtain ⟨u,hu⟩ := hC e.val e.property
    obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp e.val.property
    have hue : u ∈ {a,b} := he ▸ (Finset.mem_inter.mp hu).1
    simp only [Finset.mem_insert,Finset.mem_singleton] at hue
    rcases hue with ha | hb
    · exact ⟨u,b,(Finset.mem_inter.mp hu).2,by simpa [ha] using hab,by simpa [ha] using he⟩
    · exact ⟨u,a,(Finset.mem_inter.mp hu).2,by simpa [hb] using hab.symm,
        by simpa [hb] using he.trans (Finset.pair_comm _ _)⟩
  choose u v hu huv hedge using hp
  let f : G → C × V := fun e => (⟨u e,hu e⟩,v e)
  have hi : Function.Injective f := by
    intro e g h
    have h1 : u e=u g := congrArg (fun z : C × V => z.1.val) h
    have h2 : v e=v g := congrArg (fun z : C × V => z.2) h
    apply Subtype.ext
    apply Subtype.ext
    rw [hedge e,hedge g,h1,h2]
  have hh := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe,Fintype.card_prod] using hh

theorem graph_card_le_twice_vertices_rank (G : Graph V) :
    G.card ≤ 2 * Fintype.card V * rank G := by
  obtain ⟨M,hMG,hM,hcard⟩ := rank_attained G
  have hC (e : Edge V) (he : e ∈ G) : (e.val ∩ covered M).Nonempty :=
    closed_edge_meets_maximum hMG hM hcard (by rw [Finset.insert_eq_of_mem he])
  have hh := graph_card_le_cover G (covered M) hC
  rw [covered_card hM,hcard] at hh
  nlinarith

theorem graph_card_le_twice_vertices_opt (G : Graph V) (w : Edge V → ℕ)
    (hw : ∀ e ∈ G, 1 ≤ w e) :
    G.card ≤ 2 * Fintype.card V * natOpt w G := by
  have hro : rank G ≤ natOpt w G := by
    obtain ⟨M,hMG,hM,hcard⟩ := rank_attained G
    have hmass : M.card ≤ ∑ e ∈ M,w e := by
      calc
        _ = ∑ _e ∈ M, (1:ℕ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun e he => hw e (hMG he))
    rw [hcard] at hmass
    exact hmass.trans (matching_weight_le_natOpt w hMG hM)
  exact (graph_card_le_twice_vertices_rank G).trans (Nat.mul_le_mul_left _ hro)

/-- The nonexact full-buffer condition forces enough ORIGINAL optimum mass
for the prefix tail, using the actual graph-size theorem above. -/
theorem prefix_exponent_from_nonexact_buffer (G : Graph V) (w : Edge V → ℕ)
    (hw : ∀ e ∈ G,1 ≤ w e) (hn : 0 < Fintype.card V)
    (ρ W L : ℝ) (hρ : 0 < ρ) (hW : 0 < W)
    (hbuffer : 6*(Fintype.card V : ℝ)*W*L/ρ < G.card) :
    Real.exp (-ρ*(natOpt w G : ℝ)/(3*W)) ≤ Real.exp (-L) := by
  have hc : (G.card : ℝ) ≤ 2*(Fintype.card V : ℝ)*natOpt w G := by
    exact_mod_cast graph_card_le_twice_vertices_opt G w hw
  have hb := (div_lt_iff₀ hρ).mp hbuffer
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hc' := mul_le_mul_of_nonneg_right hc hρ.le
  have hm : 3*W*L < ρ*(natOpt w G : ℝ) := by
    nlinarith
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ)<3*W)).mpr
  nlinarith

end RandomOrderMatching.Acquisition.Probability
