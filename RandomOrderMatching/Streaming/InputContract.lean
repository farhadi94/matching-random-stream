import RandomOrderMatching.Streaming.CanonicalFailure
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Weights.Windows
open RandomOrderMatching.Graph.WeightedMatching RandomOrderMatching.Phases.WeightedState
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem natOpt_congr_on (w z : Edge V → ℕ) (G : Graph V)
    (h : ∀ e ∈ G,w e=z e) : natOpt w G=natOpt z G := by
  unfold natOpt
  apply Finset.sup_congr rfl
  intro M hM
  split_ifs
  · apply Finset.sum_congr rfl
    intro e he
    exact h e ((Finset.mem_powerset.mp hM) he)
  · rfl

theorem clippedWeight_opt (w : Edge V → ℕ) (W : ℕ) (l : List (Edge V))
    (hw : ∀ e ∈ l,w e ≤ W) :
    opt (fun e => (clippedWeight w W e:ℝ)) l.toFinset=opt (fun e => (w e:ℝ)) l.toFinset := by
  rw [opt_eq_natOpt,opt_eq_natOpt]
  congr 1
  exact natOpt_congr_on _ _ _ (fun e he => clippedWeight_eq w W e (hw e (List.mem_toFinset.mp he)))

theorem canonicalMachine_good_iff_clipped_opt (W L LU L0 : ℕ)
    (hW : 0 < W) (hL : 0 < L) (alpha : ℝ) (ha : 0 ≤ alpha)
    (w : Edge V → ℕ) (l : List (Edge V)) (hw : ∀ e ∈ l,w e ≤ W) :
    (canonicalMachine (V:=V) W L LU L0 hW hL).Good alpha w l ↔
      alpha*opt (fun e => (clippedWeight w W e:ℝ)) l.toFinset ≤
        ∑ e ∈ finalBoundedOutput (clippedWeight w W) W L LU L0
          (clippedWeight_le w W) hW hL l,(clippedWeight w W e:ℝ) := by
  rw [machine_good_iff_opt _ alpha ha,canonicalMachine_answer,clippedWeight_opt w W l hw]
  rw [←clampedBoundedOutput_weight w W L LU L0 hW hL l hw]
  rfl

/-- All operational/domain/sample-space work needed by the range compiler.
The remaining hypothesis is a finite uniform-permutation probability bound
for the actual globally bounded execution, only on the nonexact branch. -/
theorem canonicalMachine_contract_of_uniform_nonexact
    (W L LU L0 : ℕ) (hW : 0 < W) (hL : 0 < L)
    (alpha delta : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hd : 0 ≤ delta)
    (hs : ∀ {m : ℕ}, 0 < m → (w : Edge V → ℕ) → (hw : ∀ e,w e ≤ W) →
      (label : Fin m → Edge V) → Function.Injective label →
      (∀ e ∈ Finset.univ.image label,1 ≤ w e) →
      fullCapacity (Fintype.card V) (canonicalBudget V W L) W L0 < m →
      ((Finset.univ.filter (fun pi : Equiv.Perm (Fin m) =>
        (∑ e ∈ finalBoundedOutput w W L LU L0 hw hW hL (labelledStream label pi),(w e:ℝ)) <
          alpha*opt (fun e => (w e:ℝ)) (Finset.univ.image label))).card:ℝ)/
        Fintype.card (Equiv.Perm (Fin m)) ≤ delta) :
    (canonicalMachine (V:=V) W L LU L0 hW hL).Contract W alpha delta := by
  refine ⟨canonicalMachine_valid W L LU L0 hW hL,?_⟩
  intro w l hnd hw
  by_cases hfull : l.length ≤ fullCapacity (Fintype.card V) (canonicalBudget V W L) W L0
  · rw [canonicalMachine_full_failure_zero W L LU L0 hW hL alpha ha1 w l
      (fun e he => (hw e he).2) hfull]
    exact hd
  have hlarge := lt_of_not_ge hfull
  have hm : 0 < l.length := (Nat.zero_le _).trans_lt hlarge
  let wc := clippedWeight w W
  have hpos : ∀ e ∈ Finset.univ.image l.get,1 ≤ wc e := by
    intro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    have hh := hw (l.get i) (List.get_mem l i)
    rw [show wc (l.get i)=w (l.get i) from clippedWeight_eq w W _ hh.2]
    exact hh.1
  have hh := hs hm wc (clippedWeight_le w W) l.get hnd.injective_get hpos hlarge
  rw [permMean_failure_fraction l hnd]
  have he : (Finset.univ.filter (fun pi : Equiv.Perm (Fin l.length) =>
      ¬(canonicalMachine (V:=V) W L LU L0 hW hL).Good alpha w (labelledStream l.get pi))) =
      Finset.univ.filter (fun pi : Equiv.Perm (Fin l.length) =>
        (∑ e ∈ finalBoundedOutput wc W L LU L0 (clippedWeight_le w W) hW hL
          (labelledStream l.get pi),(wc e:ℝ)) <
          alpha*opt (fun e => (wc e:ℝ)) (Finset.univ.image l.get)) := by
    apply Finset.filter_congr
    intro pi _
    have hp : (labelledStream l.get pi).Perm l := by
      simpa only [List.ofFn_get] using labelledStream_perm l.get hnd.injective_get pi
    rw [canonicalMachine_good_iff_clipped_opt W L LU L0 hW hL alpha ha w
      (labelledStream l.get pi) (fun e he => (hw e (hp.mem_iff.mp he)).2),not_le,
      labelledStream_toFinset]
  rw [he]
  exact hh

end RandomOrderMatching.Streaming
#print axioms RandomOrderMatching.Streaming.canonicalMachine_contract_of_uniform_nonexact
