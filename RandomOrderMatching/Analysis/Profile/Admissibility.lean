import RandomOrderMatching.Analysis.Profile.FeasibleBound

/-! Local degree/bin conditions imply admissibility of every actual
vertex, benchmark-pair and reference-edge column. -/
noncomputable section
namespace RandomOrderMatching.Analysis.Profile
open RandomOrderMatching.Certificates.DegreeProfile

theorem vertex_center_bin {B U : Type*} {q} (d : Coordinates B U q)
    (v : Vertex B U) (c : CenterClass q) (h : vertexColumn d v=.center c) :
    c.1=d.bin v := by
  cases v with
  | inl z =>
    rcases z with ⟨i,t⟩
    fin_cases t <;> cases hk : d.kind i <;>
      simp [vertexColumn,hk,leftColumn,rightColumn] at h <;>
      subst c <;> rfl
  | inr u => cases hu : d.unmatchedCenter u <;>
      simp [vertexColumn,hu] at h <;> subst c <;> rfl

theorem vertex_outside_bin {B U : Type*} {q} (d : Coordinates B U q)
    (v : Vertex B U) (x : OutsideClass q) (h : vertexColumn d v=.outside x) :
    x.1=d.bin v := by
  cases v with
  | inl z =>
    rcases z with ⟨i,t⟩
    fin_cases t <;> cases hk : d.kind i <;>
      simp [vertexColumn,hk,leftColumn,rightColumn] at h <;>
      subst x <;> rfl
  | inr u => cases hu : d.unmatchedCenter u <;>
      simp [vertexColumn,hu] at h <;> subst x <;> rfl

theorem orderedRoot_allowed {q} (data : ProfileData q) (x y : OutsideClass q)
    (hx : outsideAllowed data x) (hy : outsideAllowed data y)
    (htx : x.2.1=.S) (hty : y.2.1=.S)
    (hdegree : 1-data.lam ≤ upper data x.1+upper data y.1) :
    columnAllowed data (orderedRoot x y) := by
  unfold orderedRoot
  split_ifs with h
  · exact ⟨hx,hy,htx,hty,h,hdegree⟩
  · exact ⟨hy,hx,hty,htx,le_of_not_ge h,by simpa [add_comm] using hdegree⟩

theorem orderedPair_I_allowed {q} (data : ProfileData q) (i j : Fin q)
    (hdegree : lower data i+lower data j ≤ 1) :
    columnAllowed data (orderedPair (i,.I) (j,.I)) := by
  unfold orderedPair
  split_ifs with h
  · exact ⟨h,rfl,Or.inl ⟨rfl,hdegree⟩⟩
  · exact ⟨le_of_not_ge h,rfl,Or.inl ⟨rfl,by simpa [add_comm] using hdegree⟩⟩

theorem orderedPair_J_allowed {q} (data : ProfileData q) (i j : Fin q)
    (hdegree : 1-data.lam ≤ upper data i+upper data j) :
    columnAllowed data (orderedPair (i,.J) (j,.J)) := by
  unfold orderedPair
  split_ifs with h
  · exact ⟨h,rfl,Or.inr ⟨rfl,hdegree⟩⟩
  · exact ⟨le_of_not_ge h,rfl,Or.inr ⟨rfl,by simpa [add_comm] using hdegree⟩⟩

theorem benchmark_allowed_of_bins {B U : Type*} {q} (d : Coordinates B U q)
    (data : ProfileData q)
    (hv : ∀ v, columnAllowed data (vertexColumn d v))
    (hlo : ∀ i, d.kind i=.internalAvailable →
      lower data (d.bin (.inl (i,0)))+lower data (d.bin (.inl (i,1))) ≤ 1)
    (hhi : ∀ i, d.kind i=.root ∨ d.kind i=.missing ∨ d.kind i=.internalMissing →
      1-data.lam ≤ upper data (d.bin (.inl (i,0)))+upper data (d.bin (.inl (i,1))))
    (i : B) : columnAllowed data (benchmarkColumn d i) := by
  have h0 := hv (.inl (i,0))
  have h1 := hv (.inl (i,1))
  cases hk : d.kind i with
  | root =>
    simp only [benchmarkColumn,hk,pairColumn]
    apply orderedRoot_allowed data _ _
    · simpa [vertexColumn,hk,leftColumn,columnAllowed] using h0
    · simpa [vertexColumn,hk,rightColumn,columnAllowed] using h1
    · rfl
    · rfl
    · exact hhi i (Or.inl hk)
  | gate => simp [benchmarkColumn,hk,pairColumn,columnAllowed]
  | missing =>
    simp only [benchmarkColumn,hk,pairColumn]
    exact ⟨by simpa [vertexColumn,hk,rightColumn,columnAllowed] using h1,
      rfl,rfl,hhi i (Or.inr (Or.inl hk))⟩
  | internalAvailable => simpa only [benchmarkColumn,hk,pairColumn] using orderedPair_I_allowed data _ _ (hlo i hk)
  | internalMissing => simpa only [benchmarkColumn,hk,pairColumn] using orderedPair_J_allowed data _ _ (hhi i (Or.inr (Or.inr hk)))

theorem bin_pair_upper {beta du dv : ℝ} {a b : ℚ}
    (hbeta : 0 < beta) (hu : beta*(a : ℝ) ≤ du) (hv : beta*(b : ℝ) ≤ dv)
    (he : du+dv ≤ beta) : a+b ≤ 1 := by
  have h : (a : ℝ)+(b : ℝ) ≤ 1 := by nlinarith
  exact_mod_cast h

theorem bin_pair_lower {beta du dv : ℝ} {a b lam : ℚ}
    (hbeta : 0 < beta) (hu : du ≤ beta*(a : ℝ)) (hv : dv ≤ beta*(b : ℝ))
    (he : beta*(1-(lam : ℝ)) ≤ du+dv) : 1-lam ≤ a+b := by
  have h : 1-(lam : ℝ) ≤ (a : ℝ)+(b : ℝ) := by nlinarith
  exact_mod_cast h

theorem reference_allowed_of_bins {q} (data : ProfileData q) (u v e : Column q)
    (hRef : ReferenceCompatible u v e)
    (hu : columnAllowed data u) (hv : columnAllowed data v)
    (hcross : ∀ c x, e=.cross c x → lower data c.1+lower data x.1 ≤ 1)
    (hint : ∀ c d, e=.internal c d → centerIndex c ≤ centerIndex d ∧
      lower data c.1+lower data d.1 ≤ 1) : columnAllowed data e := by
  rcases hRef with ⟨c,d,rfl,rfl,he | he⟩ | ⟨c,x,rfl,rfl,he⟩ | ⟨c,x,rfl,rfl,he⟩
  · simpa [he,columnAllowed] using hint c d he
  · simpa [he,columnAllowed] using hint d c he
  · simpa [he,columnAllowed] using And.intro hv (hcross c x he)
  · simpa [he,columnAllowed] using And.intro hu (hcross c x he)

end RandomOrderMatching.Analysis.Profile

#print axioms RandomOrderMatching.Analysis.Profile.benchmark_allowed_of_bins
#print axioms RandomOrderMatching.Analysis.Profile.reference_allowed_of_bins
