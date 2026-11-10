import RobustMatching.R8AcquisitionProvenance
import RobustMatching.R7SupportFlowMapMatching
import RobustMatching.R8BalancedCutUnfold

/-! The actual canonical unfolding, enumerated as one deterministic copied
batch per original edge. The fallback is used only on invalid same-parent
copied edges, which never belong to a generated batch. -/
noncomputable section
open Classical
namespace RobustMatching.R8Acquisition
open RobustMatching.R2Cut RobustMatching.R7SupportFlowMap
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem endpoint_zero_ne_one (e : Edge V) : endpoint e 0≠endpoint e 1 := by
  intro h
  have := endpoint_injective e h
  norm_num at this

theorem endpoint_pair (e : Edge V) : ({endpoint e 0,endpoint e 1}:Finset V)=e.val := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact endpoint_mem e 0
    · exact endpoint_mem e 1
  · simp [e.property,endpoint_zero_ne_one e]

def canonicalEdgeSym (e : Edge V) : Sym2 V := s(endpoint e 0,endpoint e 1)

theorem canonicalEdgeSym_toFinset (e : Edge V) : (canonicalEdgeSym e).toFinset=e.val := by
  simpa only [canonicalEdgeSym,Sym2.toFinset_mk_eq] using endpoint_pair e

def canonicalCopy (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W)
    (e : Edge V) (i : Fin (w e)) : Edge (V×Fin W) :=
  ⟨{(endpoint e 0,⟨i.val,lt_of_lt_of_le i.isLt (hw e)⟩),
     (endpoint e 1,⟨w e-1-i.val,by have := hw e; have := i.isLt; omega⟩)},by
      have hn : ((endpoint e 0,⟨i.val,lt_of_lt_of_le i.isLt (hw e)⟩) : V×Fin W)≠
          (endpoint e 1,⟨w e-1-i.val,by have := hw e; have := i.isLt; omega⟩) := by
        intro h; exact endpoint_zero_ne_one e (congrArg Prod.fst h)
      simp [hn]⟩

theorem canonicalCopy_projection (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W)
    (e : Edge V) (i : Fin (w e)) : (canonicalCopy W w hw e i).val.image Prod.fst=e.val := by
  simpa [canonicalCopy] using endpoint_pair e

theorem canonicalCopy_injective (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W)
    (e : Edge V) : Function.Injective (canonicalCopy W w hw e) := by
  intro i j hij
  have hm : ((endpoint e 0,⟨i.val,lt_of_lt_of_le i.isLt (hw e)⟩) : V×Fin W)∈
      (canonicalCopy W w hw e j).val := by rw [←hij]; simp [canonicalCopy]
  simp only [canonicalCopy,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with hh | hh
  · apply Fin.ext
    exact congrArg (fun x : V×Fin W=>x.2.val) hh
  · exact (endpoint_zero_ne_one e (congrArg Prod.fst hh)).elim

def canonicalCopies (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W) (e : Edge V) :
    List (Edge (V×Fin W)) := Finset.univ.toList.map (canonicalCopy W w hw e)

def canonicalParent (W : ℕ) (fallback : Edge V) (f : Edge (V×Fin W)) : Edge V :=
  if h : (f.val.image Prod.fst).card=2 then ⟨f.val.image Prod.fst,h⟩ else fallback

theorem canonicalParent_copy (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W)
    (fallback e : Edge V) (i : Fin (w e)) :
    canonicalParent W fallback (canonicalCopy W w hw e i)=e := by
  have hp := canonicalCopy_projection W w hw e i
  unfold canonicalParent
  simp only [hp,e.property,dif_pos]

def canonicalBatchModel (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W)
    (fallback : Edge V) : BatchModel (Edge V) (V×Fin W) where
  copies := canonicalCopies W w hw
  parent := canonicalParent W fallback
  kappa := W
  parent_mem := by
    intro e f hf
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
    exact canonicalParent_copy W w hw fallback e i
  nodup := by
    intro e
    exact List.Nodup.map (canonicalCopy_injective W w hw e) (Finset.nodup_toList _)
  batch_bound := by intro e; simpa [canonicalCopies] using hw e

theorem canonicalCopies_length (W : ℕ) (w : Edge V → ℕ) (hw : ∀ e,w e≤W) (e : Edge V) :
    (canonicalCopies W w hw e).length=w e := by simp [canonicalCopies]

/-- Exact final acquisition threshold, with no rounding loss. -/
def finalAcquisitionConfig (kappa L ell cap : ℕ) (hk : 0<kappa) (hL : 0<L) (he : 0<ell) : Config where
  beta := 10^30*kappa*L
  lower := (10^30-10^21)*kappa*L
  epochLength := ell
  uCap := cap
  beta_pos := by
    have : 0<kappa*L := Nat.mul_pos hk hL
    norm_num
    simp only [Nat.mul_assoc]
    omega
  lower_gap := by
    have : 0<kappa*L := Nat.mul_pos hk hL
    norm_num
    simp only [Nat.mul_assoc]
    omega
  epoch_pos := he

theorem final_lower_exact (kappa L ell cap : ℕ) (hk : 0<kappa) (hL : 0<L) (he : 0<ell) :
    ((finalAcquisitionConfig kappa L ell cap hk hL he).lower:ℝ)=
      (1-(10:ℝ)^(-9:ℤ))*((finalAcquisitionConfig kappa L ell cap hk hL he).beta:ℝ) := by
  norm_num [finalAcquisitionConfig]
  ring

end RobustMatching.R8Acquisition
#print axioms RobustMatching.R8Acquisition.canonicalBatchModel
#print axioms RobustMatching.R8Acquisition.final_lower_exact
