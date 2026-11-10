import RobustMatching.R8StreamingWrapperDyadic
import RobustMatching.R8AcquisitionProbabilitySize
noncomputable section
namespace RobustMatching.R8StreamingWrapper
open RobustMatching.R2Cut RobustMatching.R8AcquisitionProbability
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

def fullCapacity (n Q kappa L : ℕ) : ℕ :=
  max (400000000*Q) (600000000*n*kappa*L)
def parentCapacity (Q L : ℕ) : ℕ := 400000000*Q*L
def copiedCapacity (Q kappa L : ℕ) : ℕ := kappa*parentCapacity Q L

theorem stream_length_le_square (l : List (Edge V)) (hl : l.Nodup) :
    l.length≤Fintype.card V*Fintype.card V := by
  have hh := graph_card_le_cover l.toFinset (Finset.univ:Finset V) (by
    intro e he
    simp only [Finset.inter_univ]
    exact Finset.card_pos.mp (by rw [e.property]; decide))
  simpa [List.toFinset_card_of_nodup hl] using hh

theorem selected_copy_active_on_nonexact (l : List (Edge V)) (hl : l.Nodup)
    (Q kappa L : ℕ) (hQ : 0<Q)
    (hlarge : fullCapacity (Fintype.card V) Q kappa L<l.length) :
    chosenScale l.length∈scales (Fintype.card V) Q := by
  apply chosenScale_active (stream_length_le_square l hl)
    (show 400000000*Q≤fullCapacity (Fintype.card V) Q kappa L from le_max_left _ _)
    (lt_of_lt_of_le (by positivity : 0<400000000*Q) (le_max_left _ _)) hlarge

theorem parentCapacity_exponent {Q M m L : ℕ} (hQ : 0<Q)
    (hM : 200000000*Q≤M) (hm : m < 2*M) :
    m*L≤epochLength Q M*parentCapacity Q L := by
  have he := epochLength_lower hQ hM
  calc
    m*L ≤ (2*M)*L := Nat.mul_le_mul_right _ (Nat.le_of_lt hm)
    _ = (2*L)*M := by ring
    _ ≤ (2*L)*(200000000*Q*epochLength Q M) := Nat.mul_le_mul_left _ he
    _ = _ := by unfold parentCapacity; ring

theorem parentCapacity_exp_bound {Q M m L : ℕ} (hQ : 0<Q)
    (hM : 200000000*Q≤M) (hm : m < 2*M) (hmp : 0 < m) :
    Real.exp (-(epochLength Q M:ℝ)*parentCapacity Q L/m)≤Real.exp (-(L:ℝ)) := by
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (Nat.cast_pos.mpr hmp)).mpr
  have hh : (m:ℝ)*L≤(epochLength Q M:ℝ)*parentCapacity Q L := by
    exact_mod_cast parentCapacity_exponent hQ hM hm
  linarith

theorem nonexact_prefix_exponent (l : List (Edge V)) (hl : l.Nodup)
    (w : Edge V→ℕ) (hw : ∀e∈l.toFinset,1≤w e) (hn : 0<Fintype.card V)
    (Q kappa L : ℕ) (hk : 0<kappa)
    (hlarge : fullCapacity (Fintype.card V) Q kappa L<l.length) :
    Real.exp (-(1/100000000:ℝ)*(R7WeightedPhase.natOpt w l.toFinset:ℝ)/(3*kappa))≤
      Real.exp (-(L:ℝ)) := by
  apply prefix_exponent_from_nonexact_buffer l.toFinset w hw hn
    (1/100000000) kappa L (by norm_num) (Nat.cast_pos.mpr hk)
  have hcap : 600000000*Fintype.card V*kappa*L<l.length :=
    lt_of_le_of_lt (le_max_right _ _) hlarge
  have hc : (600000000:ℝ)*Fintype.card V*kappa*L < l.toFinset.card := by
    exact_mod_cast (by simpa [List.toFinset_card_of_nodup hl] using hcap :
      600000000*Fintype.card V*kappa*L<l.toFinset.card)
  linarith

end RobustMatching.R8StreamingWrapper
