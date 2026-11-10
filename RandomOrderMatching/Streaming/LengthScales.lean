import RandomOrderMatching.Streaming.CutoffGrid
namespace RandomOrderMatching.Streaming
set_option maxHeartbeats 0

/-- Prefix-loss parameter rho=10^-8; epochs have floor(rho*M/Q) labels. -/
def epochLength (Q M : ℕ) : ℕ := M/(100000000*Q)
def chosenScale (m : ℕ) : ℕ := 2^(Nat.log 2 m)
def scales (n Q : ℕ) : Finset ℕ :=
  ((Finset.range (Nat.log 2 (n*n)+1)).image (fun j => 2^j)).filter
    (fun M => 200000000*Q≤M)

theorem chosenScale_bounds {m : ℕ} (hm : 0<m) :
    chosenScale m≤m ∧ m<2*chosenScale m := by
  have hl := Nat.pow_log_le_self 2 (by omega : m≠0)
  have hu := Nat.lt_pow_succ_log_self (by decide : 1<2) m
  simp only [pow_succ] at hu
  exact ⟨hl,by simpa [chosenScale,Nat.mul_comm] using hu⟩

theorem scales_count (n Q : ℕ) : (scales n Q).card≤Nat.log 2 (n*n)+1 := by
  exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp))

/-- Every candidate copy is specified from n,Q before the first input label.
The unique EOF dyadic scale was therefore already active on the nonexact branch. -/
theorem chosenScale_active {n Q m full : ℕ} (hm : m≤n*n)
    (hfull : 400000000*Q≤full) (hsmall : 0<full) (hlarge : full<m) :
    chosenScale m∈scales n Q := by
  have hmp : 0<m := lt_trans hsmall hlarge
  obtain ⟨hl,hu⟩ := chosenScale_bounds hmp
  have hlog : Nat.log 2 m ≤ Nat.log 2 (n*n) :=
    Nat.le_log_of_pow_le (by decide) (hl.trans hm)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨Nat.log 2 m,Finset.mem_range.mpr (by omega),rfl⟩,?_⟩
  omega

theorem epochLength_pos {Q M : ℕ} (hQ : 0<Q) (hM : 200000000*Q≤M) :
    0<epochLength Q M := by
  unfold epochLength
  apply Nat.div_pos
  · nlinarith
  · positivity

theorem epochLength_lower {Q M : ℕ} (hQ : 0<Q) (hM : 200000000*Q≤M) :
    M≤200000000*Q*epochLength Q M := by
  have hd : 0<100000000*Q := by positivity
  have hlt := Nat.lt_mul_div_succ M hd
  have hdiv : 1≤M/(100000000*Q) := Nat.div_pos (by nlinarith) hd
  unfold epochLength
  nlinarith

theorem epochLength_prefix_bound {Q M m : ℕ} (hM : M≤m) :
    100000000*(Q*epochLength Q M)≤m := by
  have h := Nat.div_mul_le_self M (100000000*Q)
  unfold epochLength
  nlinarith

theorem chosen_freeze_prefix {Q m freeze : ℕ} (hm : 0<m)
    (hf : freeze≤Q*epochLength Q (chosenScale m)) :
    100000000*freeze≤m := by
  have hb := epochLength_prefix_bound (Q:=Q) (chosenScale_bounds hm).1
  nlinarith

end RandomOrderMatching.Streaming
