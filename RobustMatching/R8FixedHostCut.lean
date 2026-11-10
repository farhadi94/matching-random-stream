import RobustMatching.R8FixedHostCoordinates
import RobustMatching.R8BalancedCutActual
import RobustMatching.R7SupportFlowMapComplete

/-! The analytic cover and every degree hypothesis of the actual profile
certificate are obtained from the acquisition upper/lower inequalities. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
namespace RobustMatching.R8FixedHost
open R2Cut R7SupportFlowMap R8BalancedCut R2BalancedCut R7ClosedRepair.TypedLabeling
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edgeDegree_oriented (H : Graph V) (C : Finset V) (e : Edge V) :
    (R8Acquisition.edgeDegree H e:ℝ)=incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1) := by
  have hn : orientedEndpoint C e 0≠orientedEndpoint C e 1 := by
    intro hh; have hi := orientedEndpoint_injective C e hh; norm_num at hi
  rw [edgeDegree_of_adj H e _ _ hn (oriented_endpoint_pair C e).symm]
  simp only [incidenceDegree_eq_simpleGraph]

theorem covered_available_kind (A : Graph V) (C : Finset V)
    (hc : ∀e∈A,(e.val∩C).Nonempty) (e : Edge V) (he : e∈A) :
    actualPairKind C A e=.gate ∨ actualPairKind C A e=.internalAvailable := by
  have h0 : orientedEndpoint C e 0∈C := by
    obtain ⟨v,hvc⟩ := hc e he
    obtain ⟨hv,hc⟩ := Finset.mem_inter.mp hvc
    have hv' : v∈({orientedEndpoint C e 0,orientedEndpoint C e 1}:Finset V) := by
      rw [oriented_endpoint_pair]; exact hv
    rcases Finset.mem_insert.mp hv' with h | h
    · simpa [h] using hc
    · apply oriented_center_first C e
      simpa [Finset.mem_singleton.mp h] using hc
  by_cases h1 : orientedEndpoint C e 1∈C <;> simp [actualPairKind,h0,h1,he]

theorem missing_kind_not_available (A : Graph V) (C : Finset V)
    (hc : ∀e∈A,(e.val∩C).Nonempty) (e : Edge V)
    (hk : actualPairKind C A e=.root ∨ actualPairKind C A e=.missing ∨
      actualPairKind C A e=.internalMissing) : e∉A := by
  intro he
  have hh := covered_available_kind A C hc e he
  rcases hh with hh|hh <;> rw [hh] at hk <;> simp at hk

theorem internal_available_mem (A : Graph V) (C : Finset V) (e : Edge V)
    (hk : actualPairKind C A e=.internalAvailable) : e∈A := by
  by_contra he
  simp only [actualPairKind,if_neg he] at hk
  split_ifs at hk

theorem copied_benchmark_crosses {W : ℕ} (M : Graph V) (MC : Graph (V×Fin W))
    (parent : ∀e∈MC,∃f∈M,e.val.image Prod.fst=f.val)
    (z : V→Bool) (hz : ∀e∈M,∀u∈e.val,∀v∈e.val,u≠v→z u≠z v) :
    ∀e∈MC,∀u∈e.val,∀v∈e.val,u≠v→z u.1≠z v.1 := by
  intro e he u hu v hv hne
  obtain ⟨f,hf,hp⟩ := parent e he
  have hi : Set.InjOn Prod.fst (e.val:Set (V×Fin W)) := by
    apply Finset.card_image_iff.mp
    rw [hp,f.property,e.property]
  apply hz f hf u.1 (hp ▸ Finset.mem_image_of_mem Prod.fst hu)
    v.1 (hp ▸ Finset.mem_image_of_mem Prod.fst hv)
  exact fun hh=>hne (hi hu hv hh)

/-- Starting with the actual acquisition graph and its degree inequalities,
construct the analytic cut and cover with all profile-certificate inputs. -/
theorem actual_cut_profile_geometry
    (G : SimpleGraph V) (w : Sym2 V→ℕ) (W : ℕ)
    (M : Graph V) (hM : Matching M) (MC H A N : Graph (V×Fin W))
    (hparent : ∀e∈MC,∃f∈M,e.val.image Prod.fst=f.val)
    (hH : R7GraphKonig.simpleGraph H≤unfolding G w W) (hHA : H⊆A)
    (hmissing : ∀e∈MC,e∉A→e∈N)
    (κ L : ℕ) (hk : 1≤κ) (hL : 1≤L) (n δ : ℝ)
    (hn : 2≤n) (hcard : (Fintype.card (V×Fin W):ℝ)≤n)
    (hδ : 0<δ) (hδ1 : δ<1) (hlog : Real.log (100*n/δ)≤L)
    (hupper : ∀e∈H,(R8Acquisition.edgeDegree H e:ℝ)≤beta0 κ L)
    (havailable : ∀e∈A,(R8Acquisition.edgeDegree H e:ℝ)≤beta0 κ L)
    (hlower : ∀e∈N,(1-1/10^9:ℝ)*beta0 κ L≤(R8Acquisition.edgeDegree H e:ℝ)) :
    ∃z:V→Bool, ∃C:Finset (V×Fin W),
      let H' := restrict H (fun x=>z x.1)
      let A' := restrict A (fun x=>z x.1)
      let beta := betaCut (beta0 κ L)
      (∀e∈MC,∀u∈e.val,∀v∈e.val,u≠v→z u.1≠z v.1) ∧
      (∀e∈A',(e.val∩C).Nonempty) ∧ C.card=rank A' ∧
      (∀e∈H',∃v∈e.val,v∈C) ∧
      (∀e∈H',incidenceDegree H' (orientedEndpoint C e 0)+
        incidenceDegree H' (orientedEndpoint C e 1)≤beta) ∧
      (∀e∈MC,actualPairKind C A' e=.root ∨ actualPairKind C A' e=.missing ∨
        actualPairKind C A' e=.internalMissing→beta*(1-(R7ReductionCertificate.Concrete.data.lam:ℝ))≤
        incidenceDegree H' (orientedEndpoint C e 0)+incidenceDegree H' (orientedEndpoint C e 1)) ∧
      (∀e∈MC,actualPairKind C A' e=.internalAvailable→
        incidenceDegree H' (orientedEndpoint C e 0)+incidenceDegree H' (orientedEndpoint C e 1)≤beta) := by
  obtain ⟨z,hz,hcolor,hbal,hu,hl⟩ := actual_balanced_cut G w W M hM H N hH κ L hk hL
    n δ hn hcard hδ hδ1 hlog hupper hlower
  let A' := restrict A (fun x=>z x.1)
  let C := minimumCover A' (restrict_colorable A (fun x=>z x.1))
  have hc := minimumCover_spec A' (restrict_colorable A (fun x=>z x.1))
  have hmc := copied_benchmark_crosses M MC hparent z hz
  have hrestr : ∀e∈MC,e∈A→e∈A' := by
    intro e he hea
    exact restrict_contains_matching (M:={e}) (by simpa using hea)
      (fun x=>z x.1) (by
        intro f hf
        have hh : f=e := Finset.mem_singleton.mp hf
        subst f
        exact hmc e he)
      (by simp)
  refine ⟨z,C,hmc,hc.1,hc.2,?_,?_,?_,?_⟩
  · intro e he
    have hea : e∈A' := by
      obtain ⟨heH,hecross⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨hHA heH,hecross⟩
    obtain ⟨v,hvc⟩ := hc.1 e hea
    obtain ⟨hv,hvC⟩ := Finset.mem_inter.mp hvc
    exact ⟨v,hv,hvC⟩
  · intro e he
    simpa only [edgeDegree_oriented _ C] using hu e he
  · intro e he hkind
    have hna : e∉A := fun hea=>missing_kind_not_available A' C hc.1 e hkind (hrestr e he hea)
    have heN : e∈restrict N (fun x=>z x.1) :=
      restrict_contains_matching (M:={e}) (by simpa using hmissing e he hna)
        (fun x=>z x.1) (by
          intro f hf
          have hh : f=e := Finset.mem_singleton.mp hf
          subst f
          exact hmc e he)
        (by simp)
    have hh := hl e heN
    rw [edgeDegree_oriented _ C] at hh
    convert hh using 1
    all_goals norm_num [R7ReductionCertificate.Concrete.data]
    all_goals ring
  · intro e he hkind
    have hea := restrict_subset A (fun x=>z x.1) (internal_available_mem A' C e hkind)
    have hh := arbitrary_edge_upper_from_balance H (restrict H (fun x=>z x.1)) (beta0 κ L)
      (fun x=>(hbal x).2) e (havailable e hea)
    simpa only [edgeDegree_oriented _ C] using hh

end RobustMatching.R8FixedHost
