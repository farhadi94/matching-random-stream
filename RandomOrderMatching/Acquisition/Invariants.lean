import RandomOrderMatching.Acquisition.State

noncomputable section
set_option linter.unusedSectionVars false
open Classical
namespace RandomOrderMatching.Acquisition
open RandomOrderMatching.Graph
variable {V E : Type*} [Fintype V] [DecidableEq V]

theorem acquireStep_time (cfg : Config) (s : State V) (es : List (Edge V)) :
    (acquireStep cfg s es).time=s.time+1 := by
  simp only [acquireStep]
  split_ifs <;> rfl

theorem acquireStep_ref (cfg : Config) (s : State V) (es : List (Edge V)) :
    (acquireStep cfg s es).ref=(batchUpdate cfg.beta cfg.lower s.ref es).1 := by
  simp only [acquireStep]
  split_ifs <;> rfl

theorem collectStep_time (cfg : Config) (s : State V) (es : List (Edge V)) :
    (collectStep cfg s es).time=s.time+1 := by
  simp only [collectStep]
  split_ifs <;> rfl

theorem collectStep_ref (cfg : Config) (s : State V) (es : List (Edge V)) :
    (collectStep cfg s es).ref=s.ref := by
  simp only [collectStep]
  split_ifs <;> rfl

theorem step_time (cfg : Config) (batch : E → List (Edge V)) (s : State V) (a : E) :
    (step cfg batch s a).time=s.time+1 := by
  simp only [step]
  split_ifs
  · rfl
  · exact acquireStep_time cfg s _
  · exact collectStep_time cfg s _

theorem step_upper (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (hH : Upper cfg.beta s.ref) (a : E) : Upper cfg.beta (step cfg batch s a).ref := by
  simp only [step]
  split_ifs
  · exact hH
  · rw [acquireStep_ref]
    exact batchUpdate_upper cfg.beta cfg.lower cfg.beta_pos cfg.lower_gap s.ref hH _
  · rw [collectStep_ref]
    exact hH

theorem step_saved_cap (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (hs : s.saved.card≤cfg.uCap) (a : E) : (step cfg batch s a).saved.card≤cfg.uCap := by
  simp only [step,acquireStep,collectStep]
  split_ifs <;> simp_all

theorem step_ref_subset (cfg : Config) (batch : E → List (Edge V)) (s : State V) (a : E) :
    (step cfg batch s a).ref ⊆ s.ref ∪ (batch a).toFinset := by
  simp only [step]
  split_ifs
  · exact Finset.subset_union_left
  · rw [acquireStep_ref]
    exact batchUpdate_subset cfg.beta cfg.lower s.ref _
  · rw [collectStep_ref]
    exact Finset.subset_union_left

theorem freeze_persistent (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (a : E) (tau : ℕ) (hs : s.freezeAt=some tau) :
    (step cfg batch s a).freezeAt=some tau := by
  have hn : s.freezeAt≠none := by rw [hs]; simp
  simp only [step,hn,ite_false,collectStep]
  split_ifs <;> exact hs

theorem freeze_new (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (a : E) (hs : s.freezeAt=none) :
    (step cfg batch s a).freezeAt=none ∨ (step cfg batch s a).freezeAt=some (s.time+1) := by
  simp only [step,hs,ite_true,acquireStep]
  split_ifs <;> simp_all

theorem step_freeze_valid (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (hvalid : ∀ tau,s.freezeAt=some tau → 0<tau ∧ tau ≤ s.time) (a : E) :
    ∀ tau,(step cfg batch s a).freezeAt=some tau → 0<tau ∧ tau≤(step cfg batch s a).time := by
  intro tau ht
  rw [step_time]
  cases hs : s.freezeAt with
  | none =>
    rcases freeze_new cfg batch s a hs with hn | hn
    · rw [hn] at ht; cases ht
    · have heq : s.time+1=tau := Option.some.inj (hn.symm.trans ht)
      omega
  | some t =>
    have hh := freeze_persistent cfg batch s a t hs
    have heq : t=tau := Option.some.inj (hh.symm.trans ht)
    subst t
    have hv := hvalid tau hs
    omega

theorem runFrom_append (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (as bs : List E) : runFrom cfg batch s (as++bs)=runFrom cfg batch (runFrom cfg batch s as) bs := by
  simp [runFrom,List.foldl_append]

theorem runFrom_time (cfg : Config) (batch : E → List (Edge V)) (s : State V) (as : List E) :
    (runFrom cfg batch s as).time=s.time+as.length := by
  induction as generalizing s with
  | nil => simp [runFrom]
  | cons a as ih =>
    change (runFrom cfg batch (step cfg batch s a) as).time=_
    rw [ih,step_time]
    simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem run_time (cfg : Config) (batch : E → List (Edge V)) (as : List E) :
    (run cfg batch as).time=as.length := by
  simpa [run,initialState] using runFrom_time cfg batch initialState as

theorem runFrom_upper (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (hH : Upper cfg.beta s.ref) (as : List E) : Upper cfg.beta (runFrom cfg batch s as).ref := by
  induction as generalizing s with
  | nil => exact hH
  | cons a as ih => exact ih _ (step_upper cfg batch s hH a)

theorem run_upper (cfg : Config) (batch : E → List (Edge V)) (as : List E) :
    Upper cfg.beta (run cfg batch as).ref :=
  runFrom_upper cfg batch initialState (by simp [Upper,initialState]) as

theorem runFrom_saved_cap (cfg : Config) (batch : E → List (Edge V)) (s : State V)
    (hs : s.saved.card≤cfg.uCap) (as : List E) : (runFrom cfg batch s as).saved.card≤cfg.uCap := by
  induction as generalizing s with
  | nil => exact hs
  | cons a as ih => exact ih _ (step_saved_cap cfg batch s hs a)

theorem run_saved_cap (cfg : Config) (batch : E → List (Edge V)) (as : List E) :
    (run cfg batch as).saved.card≤cfg.uCap :=
  runFrom_saved_cap cfg batch initialState (by simp [initialState]) as

theorem run_reference_cap (cfg : Config) (batch : E → List (Edge V)) (as : List E) :
    2*(run cfg batch as).ref.card≤Fintype.card V*cfg.beta :=
  upper_edge_count cfg.beta (run_upper cfg batch as)

theorem stateAt_time (cfg : Config) (batch : E → List (Edge V)) (stream : ℕ → E) (k : ℕ) :
    (stateAt cfg batch stream k).time=k := by simp [stateAt,run_time,inputPrefix]

theorem stateAt_succ (cfg : Config) (batch : E → List (Edge V)) (stream : ℕ → E) (k : ℕ) :
    stateAt cfg batch stream (k+1)=step cfg batch (stateAt cfg batch stream k) (stream k) := by
  simp [stateAt,inputPrefix,List.range_succ,run,runFrom,List.foldl_append]

theorem stateAt_eq_of_prefix (cfg : Config) (batch : E → List (Edge V))
    (stream other : ℕ → E) (k : ℕ) (h : ∀ i<k,stream i=other i) :
    stateAt cfg batch stream k=stateAt cfg batch other k := by
  unfold stateAt inputPrefix
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

end RandomOrderMatching.Acquisition
#print axioms RandomOrderMatching.Acquisition.run_reference_cap
#print axioms RandomOrderMatching.Acquisition.run_saved_cap
#print axioms RandomOrderMatching.Acquisition.stateAt_eq_of_prefix
