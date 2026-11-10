import RandomOrderMatching.Probability.ClockCoupling.Transfer
import RandomOrderMatching.Streaming.CutoffSelection
import RandomOrderMatching.Phases.Execution.Output

/-! The actual physical list used by a coupled uniform suffix, with exact
prefix/suffix membership consequences of the original-label count bracket. -/
noncomputable section
set_option linter.unusedSectionVars false
open Classical
namespace RandomOrderMatching.Analysis.FixedHost
open RandomOrderMatching.Graph RandomOrderMatching.Analysis.Repair.Probability RandomOrderMatching.Probability.ClockCoupling RandomOrderMatching.Phases.Execution
variable {V B : Type*} [DecidableEq V]

def suffixStream {n : ℕ} (original : B→Edge V) (e : Fin n≃B)
    (σ : Equiv.Perm (Fin n)) : List (Edge V) :=
  List.ofFn (fun i=>original (e (σ i)))

@[simp] theorem suffixStream_length {n : ℕ} (original : B→Edge V) (e : Fin n≃B)
    (σ : Equiv.Perm (Fin n)) : (suffixStream original e σ).length=n := by
  simp [suffixStream]

theorem suffixStream_mem {n : ℕ} (original : B→Edge V) (e : Fin n≃B)
    (σ : Equiv.Perm (Fin n)) (b : B) : original b∈suffixStream original e σ := by
  apply List.mem_ofFn.mpr
  exact ⟨σ.symm (e.symm b),by simp⟩

theorem suffixStream_nodup {n : ℕ} (original : B→Edge V) (e : Fin n≃B)
    (hinj : Function.Injective original) (σ : Equiv.Perm (Fin n)) :
    (suffixStream original e σ).Nodup :=
  List.nodup_ofFn.mpr (hinj.comp (e.injective.comp σ.injective))

theorem suffixStream_toFinset [Fintype B] {n : ℕ} (original : B→Edge V) (e : Fin n≃B)
    (σ : Equiv.Perm (Fin n)) :
    (suffixStream original e σ).toFinset=Finset.univ.image original := by
  ext f
  simp only [List.mem_toFinset,suffixStream,List.mem_ofFn,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨e (σ i),hi⟩
  · rintro ⟨b,hb⟩
    exact ⟨σ.symm (e.symm b),by simpa using hb⟩

theorem suffixStream_before {n : ℕ} (original : B→Edge V) (e : Fin n≃B)
    (σ : Equiv.Perm (Fin n)) (b : B) (c : ℕ)
    (h : (σ.symm (e.symm b)).val<c) : original b∈(suffixStream original e σ).take c := by
  let i := σ.symm (e.symm b)
  apply List.mem_take_iff_getElem.mpr
  refine ⟨i.val,by simp only [suffixStream_length]; exact lt_min h i.isLt,?_⟩
  simp [suffixStream,i]

theorem suffixStream_after {n : ℕ} (original : B→Edge V) (e : Fin n≃B)
    (σ : Equiv.Perm (Fin n)) (b : B) (c : ℕ)
    (h : c≤(σ.symm (e.symm b)).val) : original b∈(suffixStream original e σ).drop c := by
  let i := σ.symm (e.symm b)
  apply List.mem_drop_iff_getElem.mpr
  refine ⟨i.val-c,by simp only [suffixStream_length]; have := i.isLt; omega,?_⟩
  have hi : c+(i.val-c)=i.val := Nat.add_sub_of_le h
  simp [suffixStream,hi,i]

theorem coupled_physical_chronology {n : ℕ} (original : B→Edge V) (e : Fin n≃B)
    (s : (Fin n→Clock)×Equiv.Perm (Fin n)) (c : ℕ)
    (hb : cutoffBracket c (coupledClocks s)) :
    (∀b,activeBit (labeledClocks e s b)=true→
      original b∈(suffixStream original e (coupledOrder s)).take c) ∧
    (∀b,earlyBit (labeledClocks e s b)=false→
      original b∈(suffixStream original e (coupledOrder s)).drop c) := by
  obtain ⟨ha,hl⟩ := labeled_bracket_chronology e s c hb
  constructor
  · intro b hh
    apply suffixStream_before original e (coupledOrder s) b c
    exact ha b (by simpa [activeBit] using hh)
  · intro b hh
    apply suffixStream_after original e (coupledOrder s) b c
    exact hl b (by simpa [earlyBit] using hh)

theorem selected_phase_active {n : ℕ} (hn : 10000000≤n)
    (original : B→Edge V) (e : Fin n≃B) (σ : Equiv.Perm (Fin n)) :
    RandomOrderMatching.Streaming.selectedCutoff n∈activeCuts (RandomOrderMatching.Streaming.reachedCuts n)
      (suffixStream original e σ) := by
  have hc := RandomOrderMatching.Streaming.selected_cutoff_reached hn
  have hh := RandomOrderMatching.Streaming.selected_cutoff_clock_bracket hn
  apply Finset.mem_filter.mpr
  refine ⟨hc,?_⟩
  rw [suffixStream_length]
  have hnr : (0:ℝ)≤n := Nat.cast_nonneg _
  have hh' : (RandomOrderMatching.Streaming.selectedCutoff n:ℝ)≤n := by linarith [hh.2]
  exact_mod_cast hh'

end RandomOrderMatching.Analysis.FixedHost
