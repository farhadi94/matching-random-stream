import RandomOrderMatching.Acquisition.BatchUpdates

/-! Concrete causal acquisition state. The copied graph is supplied by a
fixed original-batch model; this file introduces no alternative unfolding. -/
noncomputable section
open Classical
namespace RandomOrderMatching.Acquisition
open RandomOrderMatching.Graph
variable {V E : Type*} [Fintype V] [DecidableEq V]

structure Config where
  beta : ℕ
  lower : ℕ
  epochLength : ℕ
  uCap : ℕ
  beta_pos : 1≤beta
  lower_gap : lower+1≤beta
  epoch_pos : 0<epochLength

structure BatchModel (E V : Type*) [DecidableEq V] where
  copies : E → List (Edge V)
  parent : Edge V → E
  kappa : ℕ
  parent_mem : ∀ a e,e ∈ copies a → parent e=a
  nodup : ∀ a,(copies a).Nodup
  batch_bound : ∀ a,(copies a).length≤kappa

structure State (V : Type*) [DecidableEq V] where
  ref : Graph V
  time : ℕ
  pos : ℕ
  epochs : ℕ
  dirty : Bool
  freezeAt : Option ℕ
  saved : Finset (Edge V × ℕ)
  aborted : Bool

def initialState : State V := ⟨∅,0,0,0,false,none,∅,false⟩

def underfullRecords (lower : ℕ) (H : Graph V) (es : List (Edge V)) (stamp : ℕ) :
    Finset (Edge V × ℕ) :=
  (es.toFinset.filter (fun e => edgeDegree H e<lower)).image (fun e => (e,stamp))

def acquireStep (cfg : Config) (s : State V) (es : List (Edge V)) : State V :=
  let update := batchUpdate cfg.beta cfg.lower s.ref es
  let dirty := s.dirty || update.2
  if s.pos+1=cfg.epochLength then
    if dirty then
      {s with ref:=update.1,time:=s.time+1,pos:=0,epochs:=s.epochs+1,dirty:=false}
    else
      {s with ref:=update.1,time:=s.time+1,pos:=0,dirty:=false,freezeAt:=some (s.time+1)}
  else
    {s with ref:=update.1,time:=s.time+1,pos:=s.pos+1,dirty:=dirty}

def collectStep (cfg : Config) (s : State V) (es : List (Edge V)) : State V :=
  let records := s.saved ∪ underfullRecords cfg.lower s.ref es (s.time+1)
  if records.card≤cfg.uCap then {s with time:=s.time+1,saved:=records}
  else {s with time:=s.time+1,saved:=∅,aborted:=true}

/-- Abort permanently suppresses new records. The bounded frozen reference
may remain allocated; the U store is released at overflow. -/
def step (cfg : Config) (batch : E → List (Edge V)) (s : State V) (a : E) : State V :=
  if s.aborted then {s with time:=s.time+1}
  else if s.freezeAt=none then acquireStep cfg s (batch a)
  else collectStep cfg s (batch a)

def runFrom (cfg : Config) (batch : E → List (Edge V)) (s : State V) (as : List E) : State V :=
  as.foldl (step cfg batch) s

def run (cfg : Config) (batch : E → List (Edge V)) (as : List E) : State V :=
  runFrom cfg batch initialState as

def seenCopies (batch : E → List (Edge V)) (as : List E) : Graph V :=
  (as.flatMap batch).toFinset

def savedCopies (s : State V) : Graph V := s.saved.image Prod.fst

def savedParents [DecidableEq E] (parent : Edge V → E) (s : State V) : Finset (E × ℕ) :=
  s.saved.image (fun z => (parent z.1,z.2))

def inputPrefix (stream : ℕ → E) (k : ℕ) : List E := (List.range k).map stream

def stateAt (cfg : Config) (batch : E → List (Edge V)) (stream : ℕ → E) (k : ℕ) : State V :=
  run cfg batch (inputPrefix stream k)

end RandomOrderMatching.Acquisition
