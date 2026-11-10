import RandomOrderMatching.Resources.TotalRecords

namespace RandomOrderMatching.Resources
open RandomOrderMatching.Streaming
set_option maxHeartbeats 3000000
/-- A convenient explicit polynomial majorant. `L` bounds the four logarithmic
quantities, and `B` is the constant multiplying kappa L in beta. -/
theorem configured_records_polynomial (n N beta kappa LU L0 W B L : ℕ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hk : 1 ≤ kappa)
    (hN : N ≤ n*kappa) (hbeta : beta ≤ B*kappa*L) (hB : 1 ≤ B)
    (hW : W ≤ kappa) (hLU : LU ≤ L) (hL0 : L0 ≤ L)
    (hlog : Nat.log 2 (n*n)+1 ≤ L) :
    configuredRecordBound n N beta kappa LU L0 W ≤
      100000000000000000 * B^2 * n * kappa^4 * L^5 := by
  have hb : beta^2 ≤ B^2*kappa^2*L^2 := by
    calc
      beta^2 ≤ (B*kappa*L)^2 := Nat.pow_le_pow_left hbeta 2
      _ = _ := by ring
  have hp : 1 ≤ B^2*n*kappa^3*L^2 := by
    have : 0 < B^2*n*kappa^3*L^2 := by positivity
    omega
  have hq : acquisitionBudget N beta ≤ 2*B^2*n*kappa^3*L^2 := by
    have hh := Nat.mul_le_mul hN hb
    unfold acquisitionBudget
    nlinarith only [hh,hp]
  have hu : copiedCapacity (acquisitionBudget N beta) kappa LU ≤
      800000000*B^2*n*kappa^4*L^3 := by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 400000000 hq) hLU
    have hh' := Nat.mul_le_mul_left kappa hh
    unfold copiedCapacity parentCapacity
    nlinarith only [hh']
  have hnb : N*beta ≤ B^2*n*kappa^4*L^3 := by
    have hh := Nat.mul_le_mul hN hbeta
    have hb2 : B ≤ B^2 := by nlinarith only [hB]
    have hk2 : kappa^2 ≤ kappa^4 := Nat.pow_le_pow_right (by omega) (by decide)
    have hl3 : L ≤ L^3 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < L) (show 1 ≤ 3 by decide))
    have ht := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right n hb2) hk2) hl3
    nlinarith only [hh,ht]
  have hcap : fullCapacity n (acquisitionBudget N beta) kappa L0 ≤
      800000000*B^2*n*kappa^4*L^3 := by
    apply max_le
    · have hh := Nat.mul_le_mul_left 400000000 hq
      have hkl : kappa^3*L^2 ≤ kappa^4*L^3 := by
        nlinarith only [Nat.mul_le_mul_left (kappa^3*L^2)
          (show 1 ≤ kappa*L by simpa using Nat.mul_le_mul hk hL)]
      nlinarith only [hh,Nat.mul_le_mul_left (800000000*B^2*n) hkl]
    · have hh := Nat.mul_le_mul_left (600000000*n*kappa) hL0
      have hz : n*kappa*L ≤ B^2*n*kappa^4*L^3 := by
        have hb2 : 1 ≤ B^2 := one_le_pow₀ hB
        have hk4 : kappa ≤ kappa^4 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < kappa) (show 1 ≤ 4 by decide))
        have hl3 : L ≤ L^3 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < L) (show 1 ≤ 3 by decide))
        have hmul := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right n hb2) hk4) hl3
        nlinarith only [hmul]
      nlinarith only [hh,Nat.mul_le_mul_left 600000000 hz,
        Nat.zero_le (B^2*n*kappa^4*L^3)]
  have hn2 : n/2 ≤ n := Nat.div_le_self _ _
  have hweight : W*(n/2) ≤ B^2*n*kappa^4*L^3 := by
    have hh := Nat.mul_le_mul hW hn2
    have hz : n*kappa ≤ B^2*n*kappa^4*L^3 := by
      have hk4 : kappa ≤ kappa^4 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < kappa) (show 1 ≤ 4 by decide))
      have hp' : 1 ≤ B^2*L^3 := by
        simpa using Nat.mul_le_mul (one_le_pow₀ hB : 1 ≤ B^2) (one_le_pow₀ hL : 1 ≤ L^3)
      nlinarith only [Nat.mul_le_mul_left n hk4,
        Nat.mul_le_mul_left (n*kappa^4) hp']
    nlinarith only [hh,hz]
  have hc : cutoffCountBound (n*n) ≤ 10000000*L := Nat.mul_le_mul_left _ hlog
  have hsmall : 10000000 ≤ 10000000*B^2*n*kappa^4*L^3 := by
    have hpos : 0 < B^2*n*kappa^4*L^3 := by positivity
    nlinarith only [hpos]
  have hr : localRecordBound N n beta
      (copiedCapacity (acquisitionBudget N beta) kappa LU) W (n*n) ≤
      10000000000000000*B^2*n*kappa^4*L^4 := by
    have hm := Nat.mul_le_mul hc (Nat.add_le_add (Nat.add_le_add hnb hu) hweight)
    unfold localRecordBound
    have hpow : L^3 ≤ L^4 := Nat.pow_le_pow_right (by omega) (by decide)
    nlinarith only [hnb,hu,hsmall,hm,
      Nat.mul_le_mul_left (1610000003*B^2*n*kappa^4) hpow]
  have ht := Nat.mul_le_mul hlog hr
  unfold configuredRecordBound totalRecordBound
  have hpow : L^3 ≤ L^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hnsmall : n ≤ B^2*n*kappa^4*L^5 := by
    have hp' : 0 < B^2*kappa^4*L^5 := by positivity
    nlinarith only [hp']
  nlinarith only [ht,hcap,hn2,hnsmall,
    Nat.mul_le_mul_left (800000000*B^2*n*kappa^4) hpow]

end RandomOrderMatching.Resources
