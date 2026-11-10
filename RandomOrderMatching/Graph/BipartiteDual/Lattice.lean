import Mathlib

/-! Finite bipartite dual uncrossing. These theorems prove the lattice and
finite-family envelope arguments, not existence of optimal matching duals. -/

open scoped BigOperators

namespace RandomOrderMatching.Graph.BipartiteDual

variable {L R : Type*} [Fintype L] [Fintype R]

structure Potential (L R : Type*) where
  left : L → ℝ
  right : R → ℝ

def cost (p : Potential L R) : ℝ := ∑ u, p.left u + ∑ v, p.right v

structure Feasible (E : Set (L × R)) (w : L × R → ℝ)
    (p : Potential L R) : Prop where
  left_nonneg : ∀ u, 0 ≤ p.left u
  right_nonneg : ∀ v, 0 ≤ p.right v
  edge : ∀ e ∈ E, w e ≤ p.left e.1 + p.right e.2

def join (p q : Potential L R) : Potential L R :=
  ⟨fun u ↦ max (p.left u) (q.left u), fun v ↦ min (p.right v) (q.right v)⟩

def meet (p q : Potential L R) : Potential L R :=
  ⟨fun u ↦ min (p.left u) (q.left u), fun v ↦ max (p.right v) (q.right v)⟩

omit [Fintype L] [Fintype R] in
theorem feasible_join {E : Set (L × R)} {w : L × R → ℝ}
    {p q : Potential L R} (hp : Feasible E w p) (hq : Feasible E w q) :
    Feasible E w (join p q) := by
  refine ⟨fun u ↦ le_trans (hp.left_nonneg u) (le_max_left _ _),
    fun v ↦ le_min (hp.right_nonneg v) (hq.right_nonneg v), ?_⟩
  intro e he
  rcases le_total (p.right e.2) (q.right e.2) with h | h
  · simpa [join, min_eq_left h] using
      (hp.edge e he).trans (add_le_add (le_max_left (p.left e.1) (q.left e.1)) le_rfl)
  · simpa [join, min_eq_right h] using
      (hq.edge e he).trans (add_le_add (le_max_right (p.left e.1) (q.left e.1)) le_rfl)

omit [Fintype L] [Fintype R] in
theorem feasible_meet {E : Set (L × R)} {w : L × R → ℝ}
    {p q : Potential L R} (hp : Feasible E w p) (hq : Feasible E w q) :
    Feasible E w (meet p q) := by
  refine ⟨fun u ↦ le_min (hp.left_nonneg u) (hq.left_nonneg u),
    fun v ↦ le_trans (hp.right_nonneg v) (le_max_left _ _), ?_⟩
  intro e he
  rcases le_total (p.left e.1) (q.left e.1) with h | h
  · simpa [meet, min_eq_left h] using
      (hp.edge e he).trans (add_le_add le_rfl (le_max_left (p.right e.2) (q.right e.2)))
  · simpa [meet, min_eq_right h] using
      (hq.edge e he).trans (add_le_add le_rfl (le_max_right (p.right e.2) (q.right e.2)))

theorem cost_join_add_meet (p q : Potential L R) :
    cost (join p q) + cost (meet p q) = cost p + cost q := by
  have hl : (∑ u, max (p.left u) (q.left u)) +
      (∑ u, min (p.left u) (q.left u)) = (∑ u, p.left u) + ∑ u, q.left u := by
    simp_rw [← Finset.sum_add_distrib, max_add_min]
  have hr : (∑ v, min (p.right v) (q.right v)) +
      (∑ v, max (p.right v) (q.right v)) = (∑ v, p.right v) + ∑ v, q.right v := by
    simp_rw [← Finset.sum_add_distrib, min_add_max]
  dsimp [cost, join, meet]
  linarith

theorem optimal_join_meet {E : Set (L × R)} {w : L × R → ℝ}
    {b : ℝ} {p q : Potential L R}
    (hmin : ∀ z, Feasible E w z → b ≤ cost z)
    (hp : Feasible E w p) (hq : Feasible E w q)
    (hpc : cost p = b) (hqc : cost q = b) :
    cost (join p q) = b ∧ cost (meet p q) = b := by
  have hj := hmin _ (feasible_join hp hq)
  have hm := hmin _ (feasible_meet hp hq)
  have hid := cost_join_add_meet p q
  constructor <;> linarith

/-- A finite family of optimal duals has an optimal dual dominating all of
their left coordinates. No compactness or infinite extrema are assumed. -/
theorem finite_left_envelope {E : Set (L × R)} {w : L × R → ℝ} {b : ℝ}
    (hmin : ∀ z, Feasible E w z → b ≤ cost z)
    (p : Potential L R) (hp : Feasible E w p) (hpc : cost p = b)
    (ps : List (Potential L R))
    (hps : ∀ q ∈ ps, Feasible E w q ∧ cost q = b) :
    ∃ z, Feasible E w z ∧ cost z = b ∧
      (∀ u, p.left u ≤ z.left u) ∧ (∀ q ∈ ps, ∀ u, q.left u ≤ z.left u) := by
  induction ps generalizing p with
  | nil => exact ⟨p, hp, hpc, fun _ ↦ le_rfl, by simp⟩
  | cons q qs ih =>
      have hq := hps q (by simp)
      have hjoin := (optimal_join_meet hmin hp hq.1 hpc hq.2).1
      obtain ⟨z, hz, hzc, hdom, hrest⟩ := ih (join p q)
        (feasible_join hp hq.1) hjoin (fun r hr ↦ hps r (by simp [hr]))
      refine ⟨z, hz, hzc, ?_, ?_⟩
      · intro u
        exact (le_max_left (p.left u) (q.left u)).trans (hdom u)
      · intro r hr u
        rcases List.mem_cons.mp hr with hr | hr
        · subst r
          exact (le_max_right (p.left u) (q.left u)).trans (hdom u)
        · exact hrest r hr u

/-- The symmetric finite envelope dominates every right coordinate. -/
theorem finite_right_envelope {E : Set (L × R)} {w : L × R → ℝ} {b : ℝ}
    (hmin : ∀ z, Feasible E w z → b ≤ cost z)
    (p : Potential L R) (hp : Feasible E w p) (hpc : cost p = b)
    (ps : List (Potential L R))
    (hps : ∀ q ∈ ps, Feasible E w q ∧ cost q = b) :
    ∃ z, Feasible E w z ∧ cost z = b ∧
      (∀ v, p.right v ≤ z.right v) ∧ (∀ q ∈ ps, ∀ v, q.right v ≤ z.right v) := by
  induction ps generalizing p with
  | nil => exact ⟨p, hp, hpc, fun _ ↦ le_rfl, by simp⟩
  | cons q qs ih =>
      have hq := hps q (by simp)
      have hmeet := (optimal_join_meet hmin hp hq.1 hpc hq.2).2
      obtain ⟨z, hz, hzc, hdom, hrest⟩ := ih (meet p q)
        (feasible_meet hp hq.1) hmeet (fun r hr ↦ hps r (by simp [hr]))
      refine ⟨z, hz, hzc, ?_, ?_⟩
      · intro v
        exact (le_max_left (p.right v) (q.right v)).trans (hdom v)
      · intro r hr v
        rcases List.mem_cons.mp hr with hr | hr
        · subst r
          exact (le_max_right (p.right v) (q.right v)).trans (hdom v)
        · exact hrest r hr v

def IsMatching (M : Finset (L × R)) : Prop :=
  Set.InjOn Prod.fst (M : Set (L × R)) ∧ Set.InjOn Prod.snd (M : Set (L × R))

/-- Weak duality with a disjoint left endpoint charge. Both edge sets are
genuine matchings, so no endpoint price is counted twice. -/
theorem deletion_left_bound [DecidableEq L] [DecidableEq R]
    {E : Set (L × R)} {w : L × R → ℝ} {p : Potential L R}
    (hp : Feasible E w p) {M J : Finset (L × R)}
    (hm : IsMatching M) (hj : IsMatching J) (hsub : ∀ e ∈ M, e ∈ E)
    (hd : Disjoint (M.image Prod.fst) (J.image Prod.fst)) :
    (∑ e ∈ M, w e) + (∑ e ∈ J, p.left e.1) ≤ cost p := by
  have hl : (∑ e ∈ M, p.left e.1) + (∑ e ∈ J, p.left e.1) ≤ ∑ u, p.left u := by
    rw [← Finset.sum_image (f := p.left) hm.1,
      ← Finset.sum_image (f := p.left) hj.1, ← Finset.sum_union hd]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun u _ _ ↦ hp.left_nonneg u)
  have hr : (∑ e ∈ M, p.right e.2) ≤ ∑ v, p.right v := by
    rw [← Finset.sum_image (f := p.right) hm.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ ↦ hp.right_nonneg v)
  have he : (∑ e ∈ M, w e) ≤
      (∑ e ∈ M, p.left e.1) + (∑ e ∈ M, p.right e.2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e he ↦ hp.edge e (hsub e he))
  dsimp [cost]
  linarith

theorem deletion_right_bound [DecidableEq L] [DecidableEq R]
    {E : Set (L × R)} {w : L × R → ℝ} {p : Potential L R}
    (hp : Feasible E w p) {M J : Finset (L × R)}
    (hm : IsMatching M) (hj : IsMatching J) (hsub : ∀ e ∈ M, e ∈ E)
    (hd : Disjoint (M.image Prod.snd) (J.image Prod.snd)) :
    (∑ e ∈ M, w e) + (∑ e ∈ J, p.right e.2) ≤ cost p := by
  have hr : (∑ e ∈ M, p.right e.2) + (∑ e ∈ J, p.right e.2) ≤ ∑ v, p.right v := by
    rw [← Finset.sum_image (f := p.right) hm.2,
      ← Finset.sum_image (f := p.right) hj.2, ← Finset.sum_union hd]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ ↦ hp.right_nonneg v)
  have hl : (∑ e ∈ M, p.left e.1) ≤ ∑ u, p.left u := by
    rw [← Finset.sum_image (f := p.left) hm.1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun u _ _ ↦ hp.left_nonneg u)
  have he : (∑ e ∈ M, w e) ≤
      (∑ e ∈ M, p.left e.1) + (∑ e ∈ M, p.right e.2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e he ↦ hp.edge e (hsub e he))
  dsimp [cost]
  linarith

/-- Singleton edge dual certificates can be combined without increasing
either dual objective. The mixed left/right pair covers every requested edge. -/
theorem two_envelopes_cover {E : Set (L × R)} {w : L × R → ℝ} {b : ℝ}
    (hmin : ∀ z, Feasible E w z → b ≤ cost z)
    (p : Potential L R) (hp : Feasible E w p) (hpc : cost p = b)
    (J : Finset (L × R))
    (cert : ∀ e ∈ J, ∃ q, Feasible E w q ∧ cost q = b ∧
      w e ≤ q.left e.1 + q.right e.2) :
    ∃ pL pR, Feasible E w pL ∧ Feasible E w pR ∧ cost pL = b ∧ cost pR = b ∧
      ∀ e ∈ J, w e ≤ pL.left e.1 + pR.right e.2 := by
  classical
  let f : L × R → Potential L R := fun e ↦
    if he : e ∈ J then Classical.choose (cert e he) else p
  have hf (e : L × R) (he : e ∈ J) : Feasible E w (f e) ∧ cost (f e) = b ∧
      w e ≤ (f e).left e.1 + (f e).right e.2 := by
    simpa only [f, dif_pos he] using Classical.choose_spec (cert e he)
  let ps := J.toList.map f
  have hps : ∀ q ∈ ps, Feasible E w q ∧ cost q = b := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
    have hs := hf e (Finset.mem_toList.mp he)
    exact ⟨hs.1, hs.2.1⟩
  obtain ⟨pL, hL, hcL, _, hdomL⟩ := finite_left_envelope hmin p hp hpc ps hps
  obtain ⟨pR, hR, hcR, _, hdomR⟩ := finite_right_envelope hmin p hp hpc ps hps
  refine ⟨pL, pR, hL, hR, hcL, hcR, ?_⟩
  intro e he
  have hmem : f e ∈ ps := List.mem_map.mpr ⟨e, Finset.mem_toList.mpr he, rfl⟩
  exact (hf e he).2.2.trans (add_le_add (hdomL _ hmem _) (hdomR _ hmem _))

/-- Weighted bipartite deletion cancellation from optimal dual certificates.
The two deletion matchings need not be restrictions of one common matching.
Existence of these optimal dual certificates is a separate strong-duality
interface; this theorem proves all finite uncrossing and matching accounting. -/
theorem weighted_deletion_cancellation [DecidableEq L] [DecidableEq R]
    {E : Set (L × R)} {w : L × R → ℝ} {b : ℝ}
    (hmin : ∀ z, Feasible E w z → b ≤ cost z)
    (p : Potential L R) (hp : Feasible E w p) (hpc : cost p = b)
    (J ML MR : Finset (L × R)) (hj : IsMatching J)
    (hML : IsMatching ML) (hMR : IsMatching MR)
    (hsubL : ∀ e ∈ ML, e ∈ E) (hsubR : ∀ e ∈ MR, e ∈ E)
    (hdisL : Disjoint (ML.image Prod.fst) (J.image Prod.fst))
    (hdisR : Disjoint (MR.image Prod.snd) (J.image Prod.snd))
    (cert : ∀ e ∈ J, ∃ q, Feasible E w q ∧ cost q = b ∧
      w e ≤ q.left e.1 + q.right e.2) :
    (∑ e ∈ ML, w e) + (∑ e ∈ MR, w e) + (∑ e ∈ J, w e) ≤ 2 * b := by
  obtain ⟨pL, pR, hL, hR, hcL, hcR, hcover⟩ := two_envelopes_cover hmin p hp hpc J cert
  have hdl := deletion_left_bound hL hML hj hsubL hdisL
  have hdr := deletion_right_bound hR hMR hj hsubR hdisR
  have hJ : (∑ e ∈ J, w e) ≤
      (∑ e ∈ J, pL.left e.1) + (∑ e ∈ J, pR.right e.2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hcover
  linarith

end RandomOrderMatching.Graph.BipartiteDual

#print axioms RandomOrderMatching.Graph.BipartiteDual.optimal_join_meet
#print axioms RandomOrderMatching.Graph.BipartiteDual.finite_left_envelope
#print axioms RandomOrderMatching.Graph.BipartiteDual.finite_right_envelope
#print axioms RandomOrderMatching.Graph.BipartiteDual.weighted_deletion_cancellation
