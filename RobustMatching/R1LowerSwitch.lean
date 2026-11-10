import Mathlib

/-! A degree-independent parity barrier for finite hereditary packing systems.
Weighted graph matchings are an instance: an edge has its two endpoints as
resources, and feasible sets have disjoint resources. Deleting a fixed set of
terminals restricts the feasible family.
-/

open scoped BigOperators

namespace RobustMatching.Lower

variable {E I Ω : Type*} [DecidableEq E]

def Hereditary (F : Finset E → Prop) : Prop :=
  ∀ ⦃A B⦄, A ⊆ B → F B → F A

noncomputable def feasibleSets (F : Finset E → Prop) (G : Finset E) : Finset (Finset E) := by
  classical
  exact G.powerset.filter F

theorem feasibleSets_nonempty (F : Finset E → Prop) (G : Finset E) (hF : F ∅) :
    (feasibleSets F G).Nonempty := by
  classical
  exact ⟨∅, by simp [feasibleSets, hF]⟩

noncomputable def packingOpt (F : Finset E → Prop) (hF : F ∅)
    (w : E → ℝ) (G : Finset E) : ℝ :=
  (feasibleSets F G).sup' (feasibleSets_nonempty F G hF) (fun M => ∑ e ∈ M, w e)

theorem weight_le_packingOpt (F : Finset E → Prop) (hF : F ∅)
    (w : E → ℝ) {M G : Finset E} (hM : F M) (hMG : M ⊆ G) :
    (∑ e ∈ M, w e) ≤ packingOpt F hF w G := by
  classical
  exact Finset.le_sup' (f := fun M => ∑ e ∈ M, w e)
    (by simp [feasibleSets, hM, hMG])

theorem packingOpt_attained (F : Finset E → Prop) (hF : F ∅)
    (w : E → ℝ) (G : Finset E) :
    ∃ M, M ⊆ G ∧ F M ∧ packingOpt F hF w G = ∑ e ∈ M, w e := by
  classical
  obtain ⟨M, hM, heq⟩ := Finset.exists_mem_eq_sup'
    (feasibleSets_nonempty F G hF) (fun M => ∑ e ∈ M, w e)
  simp only [feasibleSets, Finset.mem_filter, Finset.mem_powerset] at hM
  exact ⟨M, hM.1, hM.2, heq⟩

theorem packingOpt_mono (F : Finset E → Prop) (hF : F ∅)
    (w : E → ℝ) {G H : Finset E} (hGH : G ⊆ H) :
    packingOpt F hF w G ≤ packingOpt F hF w H := by
  obtain ⟨M, hMG, hM, hval⟩ := packingOpt_attained F hF w G
  rw [hval]
  exact weight_le_packingOpt F hF w hM (hMG.trans hGH)

theorem packingOpt_nonneg (F : Finset E → Prop) (hF : F ∅)
    (w : E → ℝ) (G : Finset E) : 0 ≤ packingOpt F hF w G := by
  simpa using weight_le_packingOpt F hF w hF (Finset.empty_subset G)

theorem packingOpt_family_mono (F K : Finset E → Prop) (hF : F ∅) (hK : K ∅)
    (hKF : ∀ M, K M → F M) (w : E → ℝ) (G : Finset E) :
    packingOpt K hK w G ≤ packingOpt F hF w G := by
  obtain ⟨M, hMG, hM, hval⟩ := packingOpt_attained K hK w G
  rw [hval]
  exact weight_le_packingOpt F hF w (hKF M hM) hMG

/-- Remove a switch block. `none` labels fixed background edges. -/
noncomputable def removeBlock (c : E → Option I) (i : I) (G : Finset E) : Finset E := by
  classical
  exact G.filter (fun e => c e ≠ some i)

theorem removeBlock_subset (c : E → Option I) (i : I) (G : Finset E) :
    removeBlock c i G ⊆ G := by
  classical
  exact Finset.filter_subset _ _

theorem block_loss_le_charge [DecidableEq I] (F : Finset E → Prop) (hF : F ∅)
    (hher : Hereditary F) (w : E → ℝ) (c : E → Option I) (i : I)
    (G M : Finset E) (hMG : M ⊆ G) (hM : F M)
    (hopt : packingOpt F hF w G = ∑ e ∈ M, w e) :
    packingOpt F hF w G - packingOpt F hF w (removeBlock c i G) ≤
      ∑ e ∈ M, if c e = some i then w e else 0 := by
  classical
  have hMG' : removeBlock c i M ⊆ removeBlock c i G := by
    intro e he
    simp only [removeBlock, Finset.mem_filter] at he ⊢
    exact ⟨hMG he.1, he.2⟩
  have hrem := weight_le_packingOpt F hF w
    (hher (removeBlock_subset c i M) hM) hMG'
  have hsplit : (∑ e ∈ M, w e) =
      (∑ e ∈ removeBlock c i M, w e) +
        ∑ e ∈ M, if c e = some i then w e else 0 := by
    simp only [removeBlock, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases h : c e = some i <;> simp [h]
  rw [hopt]
  linarith

/-- The deletion losses of disjoint blocks charge one optimum, independently
of vertex degrees, edge coloring, or the cardinalities of the blocks. -/
theorem packing_self_bounding [Fintype I] (F : Finset E → Prop) (hF : F ∅)
    (hher : Hereditary F) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : E → Option I) (G : Finset E) :
    (∑ i, (packingOpt F hF w G - packingOpt F hF w (removeBlock c i G))) ≤
      packingOpt F hF w G := by
  classical
  obtain ⟨M, hMG, hM, hopt⟩ := packingOpt_attained F hF w G
  calc
    _ ≤ ∑ i, ∑ e ∈ M, if c e = some i then w e else 0 :=
      Finset.sum_le_sum fun i _ => block_loss_le_charge F hF hher w c i G M hMG hM hopt
    _ = ∑ e ∈ M, ∑ i, if c e = some i then w e else 0 := Finset.sum_comm
    _ ≤ ∑ e ∈ M, w e := by
      apply Finset.sum_le_sum
      intro e he
      cases hc : c e with
      | none => simpa [hc] using hw e
      | some j => simp [hc]
    _ = _ := hopt.symm

/-- Cancellation under a sign-reversing permutation; in the Boolean cube the
permutation flips one coordinate and `χ` is full parity. -/
theorem parity_cancellation [Fintype Ω] (χ h : Ω → ℝ) (flip : Ω ≃ Ω)
    (hχ : ∀ x, χ (flip x) = -χ x) (hh : ∀ x, h (flip x) = h x) :
    ∑ x, χ x * h x = 0 := by
  have heq : (∑ x, χ x * h x) = -(∑ x, χ x * h x) := by
    calc
      _ = ∑ x, χ (flip x) * h (flip x) := (Equiv.sum_comp flip _).symm
      _ = _ := by simp_rw [hχ, hh, neg_mul]; rw [Finset.sum_neg_distrib]
  linarith

/-- Finite full-parity bound for the difference of two nested packing values.
The conclusion is unnormalized: divide by `card Ω` to obtain the expectation
bound, and use `γ = 2 |E χ(f-g)|` for uniform Boolean inputs. -/
theorem packing_parity_barrier [Fintype I] [Fintype Ω]
    (F K : Finset E → Prop) (hF : F ∅) (hK : K ∅)
    (hherF : Hereditary F) (hherK : Hereditary K)
    (hKF : ∀ M, K M → F M) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : E → Option I) (A : Ω → Finset E) (χ : Ω → ℝ)
    (flip : I → Ω ≃ Ω) (hχ : ∀ i x, χ (flip i x) = -χ x)
    (hχabs : ∀ x, |χ x| ≤ 1)
    (hlocal : ∀ i x, removeBlock c i (A (flip i x)) = removeBlock c i (A x)) :
    (Fintype.card I : ℝ) *
      |∑ x, χ x * (packingOpt F hF w (A x) - packingOpt K hK w (A x))| ≤
      ∑ x, packingOpt F hF w (A x) := by
  classical
  let f : Ω → ℝ := fun x => packingOpt F hF w (A x)
  let g : Ω → ℝ := fun x => packingOpt K hK w (A x)
  let a : I → Ω → ℝ := fun i x => f x - packingOpt F hF w (removeBlock c i (A x))
  let b : I → Ω → ℝ := fun i x => g x - packingOpt K hK w (removeBlock c i (A x))
  have ha0 : ∀ i x, 0 ≤ a i x := fun i x => sub_nonneg.mpr
    (packingOpt_mono F hF w (removeBlock_subset c i (A x)))
  have hb0 : ∀ i x, 0 ≤ b i x := fun i x => sub_nonneg.mpr
    (packingOpt_mono K hK w (removeBlock_subset c i (A x)))
  have haf : ∀ x, ∑ i, a i x ≤ f x := fun x => packing_self_bounding F hF hherF w hw c (A x)
  have hbg : ∀ x, ∑ i, b i x ≤ g x := fun x => packing_self_bounding K hK hherK w hw c (A x)
  have hgf : ∀ x, g x ≤ f x := fun x => packingOpt_family_mono F K hF hK hKF w (A x)
  have hcharge : ∀ x, |∑ i, (a i x - b i x)| ≤ f x := by
    intro x
    rw [Finset.sum_sub_distrib]
    apply abs_le.mpr
    have hsa : 0 ≤ ∑ i, a i x := Finset.sum_nonneg (fun i _ => ha0 i x)
    have hsb : 0 ≤ ∑ i, b i x := Finset.sum_nonneg (fun i _ => hb0 i x)
    constructor <;> linarith [haf x, hbg x, hgf x]
  have hcancelF : ∀ i, ∑ x, χ x * packingOpt F hF w (removeBlock c i (A x)) = 0 := by
    intro i
    exact parity_cancellation χ _ (flip i) (hχ i) (by intro x; rw [hlocal])
  have hcancelK : ∀ i, ∑ x, χ x * packingOpt K hK w (removeBlock c i (A x)) = 0 := by
    intro i
    exact parity_cancellation χ _ (flip i) (hχ i) (by intro x; rw [hlocal])
  have hid : (Fintype.card I : ℝ) * (∑ x, χ x * (f x - g x)) =
      ∑ x, χ x * (∑ i, (a i x - b i x)) := by
    have hinner : ∀ i, (∑ x, χ x * (a i x - b i x)) = ∑ x, χ x * (f x - g x) := by
      intro i
      simp only [a, b, mul_sub, Finset.sum_sub_distrib, hcancelF, hcancelK, sub_zero]
    calc
      _ = ∑ _i : I, ∑ x, χ x * (f x - g x) := by simp
      _ = ∑ i, ∑ x, χ x * (a i x - b i x) := by simp_rw [hinner]
      _ = ∑ x, ∑ i, χ x * (a i x - b i x) := Finset.sum_comm
      _ = _ := by simp_rw [Finset.mul_sum]
  calc
    _ = |(Fintype.card I : ℝ) * (∑ x, χ x * (f x - g x))| := by
      simp only [f, g, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card I : ℝ) by positivity)]
    _ = |∑ x, χ x * (∑ i, (a i x - b i x))| := congrArg abs hid
    _ ≤ ∑ x, |χ x * (∑ i, (a i x - b i x))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, f x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hχabs x)).trans (hcharge x)

/-! Concrete matching bridge. For a simple graph, take `E` to be its edges and
`ends e` to be the two endpoints. The definitions also allow set packing. -/

def ResourceMatching {V : Type*} (ends : E → Finset V) (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ d ∈ M, e ≠ d → Disjoint (ends e) (ends d)

def AvoidingMatching {V : Type*} (ends : E → Finset V) (T : Finset V)
    (M : Finset E) : Prop :=
  ResourceMatching ends M ∧ ∀ e ∈ M, Disjoint (ends e) T

theorem resourceMatching_empty {V : Type*} (ends : E → Finset V) :
    ResourceMatching ends ∅ := by simp [ResourceMatching]

theorem avoidingMatching_empty {V : Type*} (ends : E → Finset V) (T : Finset V) :
    AvoidingMatching ends T ∅ := by simp [AvoidingMatching, ResourceMatching]

theorem resourceMatching_hereditary {V : Type*} (ends : E → Finset V) :
    Hereditary (ResourceMatching ends) := by
  intro A B hAB hB e he d hd hne
  exact hB e (hAB he) d (hAB hd) hne

theorem avoidingMatching_hereditary {V : Type*} (ends : E → Finset V) (T : Finset V) :
    Hereditary (AvoidingMatching ends T) := by
  intro A B hAB hB
  exact ⟨resourceMatching_hereditary ends hAB hB.1, fun e he => hB.2 e (hAB he)⟩

/-- The finite matching theorem for a fixed terminal set, without any degree
bound. Its sole switch-topology hypothesis is that deleting block `i` makes
the graph invariant when the `i`th input bit is flipped. -/
theorem terminal_matching_parity_barrier {V : Type*} [Fintype I] [Fintype Ω]
    (ends : E → Finset V) (T : Finset V) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : E → Option I) (A : Ω → Finset E) (χ : Ω → ℝ)
    (flip : I → Ω ≃ Ω) (hχ : ∀ i x, χ (flip i x) = -χ x)
    (hχabs : ∀ x, |χ x| ≤ 1)
    (hlocal : ∀ i x, removeBlock c i (A (flip i x)) = removeBlock c i (A x)) :
    (Fintype.card I : ℝ) *
      |∑ x, χ x *
        (packingOpt (ResourceMatching ends) (resourceMatching_empty ends) w (A x) -
         packingOpt (AvoidingMatching ends T) (avoidingMatching_empty ends T) w (A x))| ≤
      ∑ x, packingOpt (ResourceMatching ends) (resourceMatching_empty ends) w (A x) := by
  exact packing_parity_barrier (ResourceMatching ends) (AvoidingMatching ends T)
    (resourceMatching_empty ends) (avoidingMatching_empty ends T)
    (resourceMatching_hereditary ends) (avoidingMatching_hereditary ends T)
    (fun _ h => h.1) w hw c A χ flip hχ hχabs hlocal

end RobustMatching.Lower

#print axioms RobustMatching.Lower.packing_self_bounding
#print axioms RobustMatching.Lower.packing_parity_barrier
#print axioms RobustMatching.Lower.terminal_matching_parity_barrier
