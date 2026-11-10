import RandomOrderMatching.Graph.EvenFactor.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace RandomOrderMatching.Graph.EvenFactor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Color a partial directed cycle by orbit-index parity. When its length is
odd, an omitted source supplies the break and the base follows that source. -/
theorem partial_cycle_coloring (I : Finset V) (c : Equiv.Perm V)
    (hc : c.IsCycle) (heven : c.support ⊆ I → Even c.support.card) :
    ∃ color : V → Fin 2, ∀ v ∈ c.support, v ∈ I → color v ≠ color (c v) := by
  have hnonempty : c.support.Nonempty := Finset.card_pos.mp (by
    have hh := hc.two_le_card_support
    omega)
  have hbase : ∃ a ∈ c.support, Even c.support.card ∨
      ∃ x ∈ c.support, x ∉ I ∧ a = c x := by
    by_cases he : Even c.support.card
    · obtain ⟨a, ha⟩ := hnonempty
      exact ⟨a, ha, Or.inl he⟩
    · have hnot : ¬c.support ⊆ I := fun h => he (heven h)
      obtain ⟨x, hx, hxI⟩ := Finset.not_subset.mp hnot
      exact ⟨c x, by simpa using hx, Or.inr ⟨x, hx, hxI, rfl⟩⟩
  obtain ⟨a, ha, hbreak⟩ := hbase
  have hcycle : c.IsCycleOn (c.support : Set V) := by
    have hs : (c.support : Set V) = {x | c x ≠ x} := by ext x; simp
    rw [hs]
    exact hc.isCycleOn
  have hpow (v : V) (hv : v ∈ c.support) :
      ∃ i < c.support.card, (c^i) a = v := hcycle.exists_pow_eq ha hv
  let index : V → ℕ := fun v => if hv : v ∈ c.support then
    Classical.choose (hpow v hv) else 0
  have hidx (v : V) (hv : v ∈ c.support) :
      index v < c.support.card ∧ (c^(index v)) a = v := by
    simpa only [index, dif_pos hv] using Classical.choose_spec (hpow v hv)
  have hsucc (v : V) (hv : v ∈ c.support) :
      index (c v) = (index v+1) % c.support.card := by
    have hcv : c v ∈ c.support := by simpa using hv
    have heq : (c^(index (c v))) a = (c^(index v+1)) a := by
      rw [(hidx (c v) hcv).2, pow_succ', Equiv.Perm.mul_apply, (hidx v hv).2]
    have hm := (hcycle.pow_apply_eq_pow_apply ha).mp heq
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hidx (c v) hcv).1] using hm
  let color : V → Fin 2 := fun v => ⟨index v % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨color, ?_⟩
  intro v hv hvI hequal
  have heq : index v % 2 = index (c v) % 2 := congrArg Fin.val hequal
  have hn := (hidx v hv).1
  have hj := hsucc v hv
  by_cases hwrap : index v+1 < c.support.card
  · rw [Nat.mod_eq_of_lt hwrap] at hj
    omega
  · have hlast : index v+1 = c.support.card := by omega
    have hz : index (c v) = 0 := by rw [hj, hlast, Nat.mod_self]
    rcases hbreak with heven | ⟨x, hx, hxI, hab⟩
    · obtain ⟨k, hk⟩ := heven
      omega
    · have hcv : c v ∈ c.support := by simpa using hv
      have hca := (hidx (c v) hcv).2
      rw [hz, pow_zero, Equiv.Perm.one_apply] at hca
      have hvx : v = x := c.injective (hca.symm.trans hab)
      exact hxI (hvx ▸ hvI)

/-- A loopless partial permutation has bipartite undirected support whenever
every completely selected permutation cycle has even length. -/
theorem partial_permutation_colorable (I : Finset V) (π : Equiv.Perm V)
    (hloop : ∀ v ∈ I, π v ≠ v)
    (heven : ∀ c ∈ π.cycleFactorsFinset,
      c.support ⊆ I → Even c.support.card) :
    (arcSupport (I.image (fun v => (v, π v)))).Colorable 2 := by
  have hcolors : ∀ c : Equiv.Perm V, ∃ color : V → Fin 2,
      c ∈ π.cycleFactorsFinset →
        ∀ v ∈ c.support, v ∈ I → color v ≠ color (c v) := by
    intro c
    by_cases hc : c ∈ π.cycleFactorsFinset
    · obtain ⟨f, hf⟩ := partial_cycle_coloring I c
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1 (heven c hc)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => 0, fun h => (hc h).elim⟩
  choose colors hcolors using hcolors
  let color : V → Fin 2 := fun v => colors (π.cycleOf v) v
  have hstep (v : V) (hv : v ∈ I) : color v ≠ color (π v) := by
    have hcv : π.cycleOf v ∈ π.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr (hloop v hv))
    have hmem : v ∈ (π.cycleOf v).support := by
      rw [Equiv.Perm.mem_support]
      simpa using hloop v hv
    have hh := hcolors (π.cycleOf v) hcv v hmem hv
    simpa only [color, Equiv.Perm.cycleOf_self_apply,
      Equiv.Perm.cycleOf_apply_self] using hh
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro u v huv
  rcases huv.2 with h | h
  · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
    have hu : x = u := congrArg Prod.fst he
    have hv : π x = v := congrArg Prod.snd he
    rw [← hu, ← hv]
    exact hstep x hx
  · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
    have hv : x = v := congrArg Prod.fst he
    have hu : π x = u := congrArg Prod.snd he
    rw [← hv, ← hu]
    exact (hstep x hx).symm

/-- The converse parity implication: a fully selected permutation cycle must
have even length in any two-coloring of the partial arc support. -/
theorem full_cycle_even_of_colorable (I : Finset V) (π : Equiv.Perm V)
    (hcol : (arcSupport (I.image (fun v => (v, π v)))).Colorable 2)
    (c : Equiv.Perm V) (hc : c ∈ π.cycleFactorsFinset)
    (hfull : c.support ⊆ I) : Even c.support.card := by
  obtain ⟨color⟩ := hcol
  have hcyc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
  have hagree := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2
  have hnonempty : c.support.Nonempty := Finset.card_pos.mp (by
    have hh := hcyc.two_le_card_support
    omega)
  obtain ⟨a, ha⟩ := hnonempty
  have hcycle : c.IsCycleOn (c.support : Set V) := by
    have hs : (c.support : Set V) = {x | c x ≠ x} := by ext x; simp
    rw [hs]
    exact hcyc.isCycleOn
  have hstep (v : V) (hv : v ∈ c.support) :
      (color v).val + (color (c v)).val = 1 := by
    have hne : v ≠ c v := (Equiv.Perm.mem_support.mp hv).symm
    have harc : (arcSupport (I.image (fun v => (v, π v)))).Adj v (c v) := by
      refine ⟨hne, Or.inl ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨v, hfull hv, by simp [hagree v hv]⟩
    have hh := color.valid harc
    have hval : (color v).val ≠ (color (c v)).val := fun he => hh (Fin.ext he)
    have h0 := (color v).isLt
    have h1 := (color (c v)).isLt
    omega
  have hindex : ∀ k : ℕ,
      (color ((c^k) a)).val = ((color a).val+k) % 2 := by
    intro k
    induction k with
    | zero => simpa using (Nat.mod_eq_of_lt (color a).isLt).symm
    | succ k ih =>
      have hmem : (c^k) a ∈ c.support := by simpa using ha
      have hs := hstep ((c^k) a) hmem
      rw [pow_succ', Equiv.Perm.mul_apply]
      rw [ih] at hs
      have hlt := (color (c ((c^k) a))).isLt
      omega
  have hperiod := hindex c.support.card
  rw [hcycle.pow_card_apply ha] at hperiod
  have hval := (color a).isLt
  refine ⟨c.support.card/2, ?_⟩
  omega

theorem partial_permutation_evenFactor (I : Finset V) (π : Equiv.Perm V)
    (hloop : ∀ v ∈ I, π v ≠ v)
    (heven : ∀ c ∈ π.cycleFactorsFinset,
      c.support ⊆ I → Even c.support.card) :
    EvenFactor (I.image (fun v => (v, π v))) := by
  refine ⟨⟨?_, ?_⟩, ?_, partial_permutation_colorable I π hloop heven⟩
  · intro e he f hf hsame
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hf
    change u = v at hsame
    subst v
    rfl
  · intro e he f hf hsame
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hf
    have huv : u = v := π.injective hsame
    subst v
    rfl
  · intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    exact (hloop u hu).symm

end RandomOrderMatching.Graph.EvenFactor

set_option pp.fullNames true
#print axioms RandomOrderMatching.Graph.EvenFactor.partial_cycle_coloring
#print axioms RandomOrderMatching.Graph.EvenFactor.partial_permutation_colorable
#print axioms RandomOrderMatching.Graph.EvenFactor.full_cycle_even_of_colorable
#print axioms RandomOrderMatching.Graph.EvenFactor.partial_permutation_evenFactor
