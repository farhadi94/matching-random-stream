import RobustMatching.R8AcquisitionGraph

/-! Actual edge insertion/deletion changes the graph potential by the
proved endpoint-update formula; the integer data are not assumed. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical
namespace RobustMatching.R8Acquisition
open RobustMatching.R2Cut
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edgeDegree_endpoints (H : Graph V) (e : Edge V) (u v : V)
    (huv : u ≠ v) (he : e.val={u,v}) : edgeDegree H e=degree H u+degree H v := by
  simp [edgeDegree,he,huv]

theorem insert_degree_update {H : Graph V} (e : Edge V) (he : e ∉ H)
    (u v : V) (huv : u ≠ v) (hev : e.val={u,v}) :
    (fun z => (degree (insert e H) z : ℤ)) =
      R1OfflinePotential.endpointUpdate (fun z => (degree H z : ℤ)) u v 1 := by
  funext z
  rw [degree_insert e he]
  push_cast
  by_cases hzu : z=u <;> by_cases hzv : z=v <;>
    simp_all [hev,R1OfflinePotential.endpointUpdate]

theorem erase_degree_update {H : Graph V} (e : Edge V) (he : e ∈ H)
    (u v : V) (huv : u ≠ v) (hev : e.val={u,v}) :
    (fun z => (degree (H.erase e) z : ℤ)) =
      R1OfflinePotential.endpointUpdate (fun z => (degree H z : ℤ)) u v (-1) := by
  funext z
  rw [degree_erase_int e he]
  by_cases hzu : z=u <;> by_cases hzv : z=v <;>
    simp_all [hev,R1OfflinePotential.endpointUpdate] <;> ring

theorem insert_potential_increase (beta : ℕ) {H : Graph V} (e : Edge V)
    (he : e ∉ H) (hdeg : (edgeDegree H e : ℤ) ≤ (beta : ℤ)-2) :
    potential beta H+1 ≤ potential beta (insert e H) := by
  obtain ⟨u,v,huv,hev⟩ := Finset.card_eq_two.mp e.property
  have hd := insert_degree_update e he u v huv hev
  have hbound : (degree H u : ℤ)+(degree H v : ℤ) ≤ (beta : ℤ)-2 := by
    rw [edgeDegree_endpoints H e u v huv hev] at hdeg
    exact_mod_cast hdeg
  have hp := R1OfflinePotential.insertion_increases (beta : ℤ) (H.card : ℤ)
    (fun z => (degree H z : ℤ)) u v huv hbound
  have hs := congrArg (fun d : V → ℤ => ∑ z,d z^2) hd
  simp only [R1OfflinePotential.potential] at hp
  unfold potential
  rw [Finset.card_insert_of_notMem he,Nat.cast_add,Nat.cast_one]
  rw [hs]
  exact hp

theorem erase_potential_increase (beta : ℕ) {H : Graph V} (e : Edge V)
    (he : e ∈ H) (hdeg : beta < edgeDegree H e) :
    potential beta H+1 ≤ potential beta (H.erase e) := by
  obtain ⟨u,v,huv,hev⟩ := Finset.card_eq_two.mp e.property
  have hd := erase_degree_update e he u v huv hev
  have hbound : (beta : ℤ)+1 ≤ (degree H u : ℤ)+(degree H v : ℤ) := by
    rw [edgeDegree_endpoints H e u v huv hev] at hdeg
    exact_mod_cast hdeg
  have hp := R1OfflinePotential.deletion_increases (beta : ℤ) (H.card : ℤ)
    (fun z => (degree H z : ℤ)) u v huv hbound
  have hs := congrArg (fun d : V → ℤ => ∑ z,d z^2) hd
  have hc : ((H.erase e).card : ℤ) = (H.card : ℤ)-1 := by
    have hcc := Finset.card_erase_add_one he
    have hh : ((H.erase e).card : ℤ)+1=(H.card : ℤ) := by exact_mod_cast hcc
    linarith
  simp only [R1OfflinePotential.potential] at hp
  unfold potential
  rw [hc,hs]
  exact hp

theorem upper_degree_bound (beta : ℕ) {H : Graph V} (hH : Upper beta H) (v : V) :
    degree H v ≤ beta := by
  by_cases hz : degree H v=0
  · omega
  · have hn : (H.filter (fun e => v ∈ e.val)).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
    obtain ⟨e,he⟩ := hn
    obtain ⟨heH,hve⟩ := Finset.mem_filter.mp he
    have hh : degree H v ≤ edgeDegree H e :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hve
    exact hh.trans (hH e heH)

theorem upper_edge_count (beta : ℕ) {H : Graph V} (hH : Upper beta H) :
    2*H.card ≤ Fintype.card V*beta := by
  rw [←degree_sum H]
  exact (Finset.sum_le_sum (fun v _ => upper_degree_bound beta hH v)).trans_eq (by simp)

end RobustMatching.R8Acquisition
#print axioms RobustMatching.R8Acquisition.insert_potential_increase
#print axioms RobustMatching.R8Acquisition.erase_potential_increase
#print axioms RobustMatching.R8Acquisition.upper_edge_count
