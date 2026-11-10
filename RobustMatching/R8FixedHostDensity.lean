import RobustMatching.R8FixedHostCoordinates
import RobustMatching.R8FixedHostSupportConsequences

/-! The nontrivial approximation branch has a large actual benchmark and
a long physical suffix. This follows from graph degrees and copy-parent
counts, without an assumed large-instance or concentration hypothesis. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators
namespace RobustMatching.R8FixedHost
open R2Cut R7ClosedRepair.TypedLabeling R7SupportFlowMap R8RepairProbability
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]
variable {q : ℕ}

theorem benchmark_le_root_add_cover (M : Graph V) (hM : Matching M)
    (C : Finset V) (A : Graph V) (bin : V→Fin q) (mask : V→Fin 4) :
    M.card≤Fintype.card (PairFiber (coordinatesFromMatching M hM C A bin mask) .root)+C.card := by
  have hm := actual_benchmark_card M hM C A bin mask
  have hc := actual_center_card M hM C A bin mask
  simp only [CanonicalBenchmark,R7ClosedRepair.Typed.Benchmarks,Fintype.card_sum] at hm
  simp only [CanonicalCenters,R7ClosedRepair.Typed.Centers,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_bool] at hc
  omega

theorem deficient_benchmark_large (M H : Graph V) (hM : Matching M)
    (C : Finset V) (A : Graph V) (bin : V→Fin q) (mask : V→Fin 4)
    (beta : ℝ) (hbeta : 0<beta)
    (hcover : ∀e∈H,∃v∈e.val,v∈C)
    (hupper : ∀e∈H,incidenceDegree H (orientedEndpoint C e 0)+
      incidenceDegree H (orientedEndpoint C e 1)≤beta)
    (hroot : ∀e∈M,actualPairKind C A e=.root→
      beta*(1-1/100000000) ≤ incidenceDegree H (orientedEndpoint C e 0)+
        incidenceDegree H (orientedEndpoint C e 1))
    (hsmall : C.card<M.card) : (49:ℝ)/100*beta≤M.card := by
  let d := coordinatesFromMatching M hM C A bin mask
  have hn := benchmark_le_root_add_cover M hM C A bin mask
  have hp : 0<Fintype.card (PairFiber d .root) := by dsimp [d]; omega
  obtain ⟨r⟩ := Fintype.card_pos_iff.mp hp
  have h0 := R8FixedHostSupport.actual_outside_degree_le_cover M hM C A bin mask
    H beta hbeta hcover hupper (.inl (r,false))
  have h1 := R8FixedHostSupport.actual_outside_degree_le_cover M hM C A bin mask
    H beta hbeta hcover hupper (.inl (r,true))
  have he0 := actual_endpoint M hM C A bin mask (.inl r) false
  have he1 := actual_endpoint M hM C A bin mask (.inl r) true
  change actualVertexEquiv M hM C A bin mask (.inr (.inl (r,false)))=
    orientedEndpoint C r.val.val 0 at he0
  change actualVertexEquiv M hM C A bin mask (.inr (.inl (r,true)))=
    orientedEndpoint C r.val.val 1 at he1
  rw [he0] at h0
  rw [he1] at h1
  have hh := hroot r.val.val r.val.property r.property
  have hs : (C.card:ℝ)<M.card := Nat.cast_lt.mpr hsmall
  nlinarith

theorem benchmark_card_le_parents (M : Graph V) (par : M→B) (κ : ℕ)
    (hfiber : ∀b,Fintype.card {e:M //par e=b}≤κ) :
    (M.card:ℝ)≤κ*Fintype.card B := by
  have heq : (M.card:ℝ)=∑b:B,∑e:M,if par e=b then (1:ℝ) else 0 := by
    rw [Finset.sum_comm]
    simp
  rw [heq]
  calc
    _≤∑_b:B,(κ:ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      have he : (∑e:M,if par e=b then (1:ℝ) else 0)=
        (Fintype.card {e:M //par e=b}:ℝ) := by simp [Fintype.card_subtype]
      rw [he]
      exact_mod_cast hfiber b
    _=κ*Fintype.card B := by simp [mul_comm]

theorem matching_card_le_vertices (M : Graph V) (hM : Matching M) :
    M.card≤Fintype.card V := by
  have hh := Finset.card_le_card (Finset.subset_univ (covered M))
  rw [covered_card hM,Finset.card_univ] at hh
  omega

theorem deficient_suffix_length {μ beta L : ℝ} {κ m : ℕ}
    (hk : 0<κ) (_hL : 0<L) (hbeta : 10^30*(κ:ℝ)*L/2≤beta)
    (hmu : (49:ℝ)/100*beta≤μ) (hparents : μ≤κ*m) :
    70000000000000000000000000000*L≤(m:ℝ) := by
  have hkr : 0<(κ:ℝ) := Nat.cast_pos.mpr hk
  have hh : (κ:ℝ)*(70000000000000000000000000000*L)≤κ*m := by nlinarith
  exact (mul_le_mul_iff_right₀ hkr).mp hh

end RobustMatching.R8FixedHost
