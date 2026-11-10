import RandomOrderMatching.Resources.TotalRecords
import RandomOrderMatching.Acquisition.Storage

/-! Finite encodings and the storage ledger. These are storage bounds and
finite encoding existence theorems, not a formal running-time or workspace
analysis of a maximum-weight matching implementation. -/
noncomputable section
open scoped BigOperators
namespace RandomOrderMatching.Resources
open RandomOrderMatching.Graph RandomOrderMatching.Streaming
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

abbrev BitWord (b : ℕ) := Fin b → Bool

def wordBits (K : ℕ) : ℕ := Nat.log 2 K + 1

theorem wordBits_capacity (K : ℕ) : K < 2 ^ wordBits K :=
  Nat.lt_pow_succ_log_self (by decide) K

theorem bits_card (b : ℕ) : Fintype.card (BitWord b) = 2^b := by
  simp [BitWord]

/-- Any explicitly finite alphabet with at most 2^b symbols has an injective
b-bit representation. No real-valued unit-cost words are used. -/
def finiteEncoding (A : Type*) [Fintype A] (b : ℕ)
    (h : Fintype.card A ≤ 2^b) : A → BitWord b :=
  fun a => (Fintype.equivFin (BitWord b)).symm
    ⟨(Fintype.equivFin A a).val,
      lt_of_lt_of_le (Fintype.equivFin A a).isLt (h.trans_eq (bits_card b).symm)⟩

theorem finiteEncoding_injective (A : Type*) [Fintype A] (b : ℕ)
    (h : Fintype.card A ≤ 2^b) : Function.Injective (finiteEncoding A b h) := by
  intro a a' hh
  apply (Fintype.equivFin A).injective
  apply Fin.ext
  have hs := congrArg (fun x => (Fintype.equivFin (BitWord b) x).val) hh
  simpa only [finiteEncoding,Equiv.apply_symm_apply] using hs

theorem bounded_counter_encoding (M : ℕ) :
    ∃ f : Fin (M+1) → BitWord (wordBits (M+1)), Function.Injective f := by
  have h : Fintype.card (Fin (M+1)) ≤ 2^wordBits (M+1) := by
    simpa using (wordBits_capacity (M+1)).le
  exact ⟨finiteEncoding _ _ h,finiteEncoding_injective _ _ h⟩

theorem edge_alphabet_card : Fintype.card (Edge V) ≤ (Fintype.card V)^2 := by
  have hh := RandomOrderMatching.Acquisition.Probability.graph_card_le_cover
    (Finset.univ : Graph V) (Finset.univ : Finset V) (by
      intro e he
      simp only [Finset.inter_univ]
      exact Finset.card_pos.mp (by rw [e.property]; decide))
  simpa [pow_two] using hh

/-- An original record contains its integer weight; a copied reference/U
record additionally contains a bounded timestamp. Endpoints use finite labels.
The disjoint sum is the one-bit record tag. -/
abbrev StoredRecord (V C : Type*) [DecidableEq V] [DecidableEq C] (W m : ℕ) :=
  (Edge V × Fin (W+1)) ⊕ ((Edge C × Fin (W+1)) × Fin (m+1))

def recordBits (n N W m : ℕ) : ℕ :=
  1 + 2*wordBits (max n N) + wordBits (W+1) + wordBits (m+1)

theorem stored_record_card (W m : ℕ) :
    Fintype.card (StoredRecord V C W m) ≤
      2 ^ recordBits (Fintype.card V) (Fintype.card C) W m := by
  let A := 2 ^ (2*wordBits (max (Fintype.card V) (Fintype.card C)))
  let B := 2 ^ wordBits (W+1)
  let D := 2 ^ wordBits (m+1)
  have hn : Fintype.card V ≤ 2^wordBits (max (Fintype.card V) (Fintype.card C)) :=
    (le_max_left _ _).trans (wordBits_capacity _).le
  have hN : Fintype.card C ≤ 2^wordBits (max (Fintype.card V) (Fintype.card C)) :=
    (le_max_right _ _).trans (wordBits_capacity _).le
  have hv : Fintype.card (Edge V) ≤ A := by
    have hh := Nat.pow_le_pow_left hn 2
    exact (edge_alphabet_card (V:=V)).trans
      (by simpa only [A,←pow_mul,Nat.mul_comm] using hh)
  have hc : Fintype.card (Edge C) ≤ A := by
    have hh := Nat.pow_le_pow_left hN 2
    exact (edge_alphabet_card (V:=C)).trans
      (by simpa only [A,←pow_mul,Nat.mul_comm] using hh)
  have hw : W+1 ≤ B := (wordBits_capacity _).le
  have hm : m+1 ≤ D := (wordBits_capacity _).le
  have hD : 1 ≤ D := one_le_pow₀ (by decide : 1≤(2:ℕ))
  have h1 := Nat.mul_le_mul hv hw
  have h2 := Nat.mul_le_mul (Nat.mul_le_mul hc hw) hm
  have h3 := Nat.mul_le_mul_left (A*B) hD
  simp only [StoredRecord,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  calc
    _ ≤ 2*A*B*D := by nlinarith
    _ = 2 ^ recordBits (Fintype.card V) (Fintype.card C) W m := by
      simp only [recordBits,pow_add,pow_one,A,B,D]

theorem stored_record_encoding (W m : ℕ) :
    ∃ f : StoredRecord V C W m →
      BitWord (recordBits (Fintype.card V) (Fintype.card C) W m), Function.Injective f :=
  ⟨finiteEncoding _ _ (stored_record_card W m),
    finiteEncoding_injective _ _ (stored_record_card W m)⟩

/-- Original rational input encodings are charged as finite payloads, rather
than treated as unit-cost real weights. `P` includes numerator and denominator. -/
theorem record_payload_encoding (W m P : ℕ) :
    ∃ f : StoredRecord V C W m × BitWord P →
      BitWord (recordBits (Fintype.card V) (Fintype.card C) W m + P),
      Function.Injective f := by
  have h : Fintype.card (StoredRecord V C W m × BitWord P) ≤
      2^(recordBits (Fintype.card V) (Fintype.card C) W m+P) := by
    rw [Fintype.card_prod,bits_card,pow_add]
    exact Nat.mul_le_mul_right _ (stored_record_card W m)
  exact ⟨finiteEncoding _ _ h,finiteEncoding_injective _ _ h⟩

/-- Fixed-capacity arrays of already encoded records have exactly additive
bit cost. The explicit length occupies one additional bounded counter. -/
theorem record_array_encoding (K b : ℕ) :
    ∃ f : Fin (K+1) × (Fin K → BitWord b) →
      BitWord (wordBits (K+1) + K*b), Function.Injective f := by
  have hc : Fintype.card (Fin (K+1) × (Fin K → BitWord b)) ≤
      2^(wordBits (K+1)+K*b) := by
    simp only [BitWord,Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,
      Fintype.card_bool,pow_add]
    have h := Nat.mul_le_mul_right ((2^b)^K) (wordBits_capacity (K+1)).le
    convert h using 1
    ring
  exact ⟨finiteEncoding _ _ hc,finiteEncoding_injective _ _ hc⟩

def metadataWords (n : ℕ) : ℕ :=
  16 + (Nat.log 2 (n*n)+1) * (16 + 4*cutoffCountBound (n*n))

def storageBitLedger (records n N W m counterMax : ℕ) : ℕ :=
  records * recordBits n N W m + metadataWords n * wordBits (counterMax+1)

theorem storageBitLedger_mono {r R : ℕ} (h : r ≤ R)
    (n N W m counterMax : ℕ) :
    storageBitLedger r n N W m counterMax ≤ storageBitLedger R n N W m counterMax :=
  Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _

/-- The exact bound on the actual complete state multiplied by finite record
width. Metadata is charged separately, with no matching-oracle workspace claim. -/
theorem configured_storage_ledger (w : Edge V → ℕ) (beta lower LU L0 W counterMax : ℕ)
    (hb : 1 ≤ beta) (hl : lower+1 ≤ beta)
    (model : RandomOrderMatching.Acquisition.BatchModel (Edge V) C) (l : List (Edge V))
    (hnd : l.Nodup) (hw : ∀ e ∈ l, w e ≤ W) :
    let n := Fintype.card V
    let N := Fintype.card C
    let Q := acquisitionBudget N beta
    let cfg := fun M => configForScale beta lower (copiedCapacity Q model.kappa LU) Q M hb hl
    storageBitLedger (outerRecordCount n Q localRecords
      (boundedIntegerRun n Q (fullCapacity n Q model.kappa L0) w cfg model l))
      n N W (n*n) counterMax ≤
    storageBitLedger (configuredRecordBound n N beta model.kappa LU L0 W)
      n N W (n*n) counterMax := by
  apply storageBitLedger_mono
  exact configured_records w beta lower LU L0 W hb hl model l hnd hw

end RandomOrderMatching.Resources
