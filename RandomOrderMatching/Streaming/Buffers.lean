import Mathlib.Tactic

/-! A hard-capped complete buffer. Overflow releases every buffered record.
The transition sees only the current state and the arriving original label. -/
namespace RandomOrderMatching.Streaming
variable {E : Type*}

def bufferStep (cap : ℕ) (s : Option (List E)) (e : E) : Option (List E) :=
  match s with
  | none => none
  | some l => if l.length<cap then some (l++[e]) else none

def bufferRun (cap : ℕ) (l : List E) : Option (List E) :=
  l.foldl (bufferStep cap) (some [])

theorem bufferRun_append (cap : ℕ) (l : List E) (e : E) :
    bufferRun cap (l++[e]) = bufferStep cap (bufferRun cap l) e := by
  simp [bufferRun,List.foldl_append]

theorem bufferRun_exact (cap : ℕ) (l : List E) :
    bufferRun cap l = if l.length≤cap then some l else none := by
  induction l using List.reverseRecOn with
  | nil => simp [bufferRun]
  | append_singleton l e ih =>
    rw [bufferRun_append,ih]
    by_cases h : l.length<cap
    · have hl : l.length≤cap := by omega
      have hs : (l++[e]).length≤cap := by simp; omega
      simp [hl,hs,bufferStep,h]
    · by_cases hl : l.length≤cap
      · have hs : ¬(l++[e]).length≤cap := by simp; omega
        simp [hl,hs,bufferStep,h]
      · have hs : ¬(l++[e]).length≤cap := by simp; omega
        simp [hl,hs,bufferStep,h]

theorem bufferRun_some_iff (cap : ℕ) (l b : List E) :
    bufferRun cap l=some b ↔ l.length≤cap ∧ b=l := by
  rw [bufferRun_exact]
  split_ifs <;> simp_all [eq_comm]

theorem bufferRun_none_iff (cap : ℕ) (l : List E) :
    bufferRun cap l=none ↔ cap<l.length := by
  rw [bufferRun_exact]
  split_ifs <;> simp_all

theorem bufferRun_hard_cap (cap : ℕ) (l b : List E)
    (hb : bufferRun cap l=some b) : b.length≤cap := by
  obtain ⟨hl,rfl⟩ := (bufferRun_some_iff cap l b).mp hb
  exact hl

theorem suffix_buffer_exact (cap freeze : ℕ) (l b : List E)
    (hb : bufferRun cap (l.drop freeze)=some b) : b=l.drop freeze :=
  ((bufferRun_some_iff cap (l.drop freeze) b).mp hb).2

end RandomOrderMatching.Streaming
