import RandomOrderMatching.Acquisition.Probability.StoppingTime
import RandomOrderMatching.Acquisition.Termination
noncomputable section
namespace RandomOrderMatching.Streaming
open RandomOrderMatching.Graph RandomOrderMatching.Acquisition RandomOrderMatching.Acquisition.Probability
variable {C E : Type*} [Fintype C] [DecidableEq C]
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

def extendList (l : List E) (d : E) (i : ℕ) : E := l.getD i d

theorem inputPrefix_extendList (l : List E) (d : E) (k : ℕ) (hk : k ≤ l.length) :
    inputPrefix (extendList l d) k=l.take k := by
  apply List.ext_getElem (by simp [inputPrefix,Nat.min_eq_left hk])
  intro i hi hj
  have hik : i < k := by simpa [inputPrefix] using hi
  have hil : i < l.length := hik.trans_le hk
  simp only [inputPrefix,List.getElem_map,List.getElem_range,List.getElem_take,extendList]
  exact (List.getElem_eq_getD (h:=hil) d).symm

theorem stateAt_extendList (cfg : Config) (batch : E→List (Edge C))
    (l : List E) (d : E) (k : ℕ) (hk : k ≤ l.length) :
    stateAt cfg batch (extendList l d) k=run cfg batch (l.take k) := by
  rw [stateAt,inputPrefix_extendList l d k hk]

theorem list_freeze_valid (cfg : Config) (batch : E→List (Edge C))
    (l : List E) (d : E) (tau : ℕ) (ht : (run cfg batch l).freezeAt=some tau) :
    0 < tau ∧ tau ≤ l.length := by
  apply actual_freeze_valid cfg batch (extendList l d) l.length tau
  simpa [stateAt_extendList cfg batch l d l.length le_rfl] using ht

theorem list_freeze_restrict (cfg : Config) (batch : E→List (Edge C))
    (l : List E) (d : E) (tau i : ℕ) (hi : i ≤ l.length) (hti : tau ≤ i)
    (ht : (run cfg batch l).freezeAt=some tau) :
    (run cfg batch (l.take i)).freezeAt=some tau := by
  have hfull : (stateAt cfg batch (extendList l d) l.length).freezeAt=some tau := by
    simpa [stateAt_extendList cfg batch l d l.length le_rfl] using ht
  have hh := actual_freeze_restrict cfg batch (extendList l d) i l.length tau hi hti hfull
  simpa only [stateAt_extendList cfg batch l d i hi] using hh

theorem list_before_freeze_none (cfg : Config) (batch : E→List (Edge C))
    (l : List E) (d : E) (tau i : ℕ) (hi : i < tau)
    (ht : (run cfg batch l).freezeAt=some tau) :
    (run cfg batch (l.take i)).freezeAt=none := by
  have hv := list_freeze_valid cfg batch l d tau ht
  have hil : i ≤ l.length := by omega
  cases hh : (run cfg batch (l.take i)).freezeAt with
  | none => rfl
  | some u =>
    have hs : (stateAt cfg batch (extendList l d) i).freezeAt=some u := by
      simpa only [stateAt_extendList cfg batch l d i hil] using hh
    have hp := actual_freeze_persists cfg batch (extendList l d) i l.length u hil hs
    have hfull : (stateAt cfg batch (extendList l d) l.length).freezeAt=some tau := by
      simpa [stateAt_extendList cfg batch l d l.length le_rfl] using ht
    have heu : u=tau := Option.some.inj (hp.symm.trans hfull)
    have hu := actual_freeze_valid cfg batch (extendList l d) i u hs
    omega

theorem run_take_append (cfg : Config) (batch : E→List (Edge C))
    (l : List E) (t i : ℕ) :
    runFrom cfg batch (run cfg batch (l.take t)) ((l.drop t).take i)=
      run cfg batch (l.take (t+i)) := by
  rw [List.take_add]
  simp [run,runFrom,List.foldl_append]

end RandomOrderMatching.Streaming
