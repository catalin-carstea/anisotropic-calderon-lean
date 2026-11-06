import Calderon.MixedKernelConstruction.MixedKernelNativeRadialSeedBoundary
import Calderon.MixedKernelConstruction.MixedKernelCurrentBootstrapMonotone
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- Higher original fronts lie in the actual seed, old STRICT outside, or SAME old front, with boundary retained. -/
theorem nativeSphereFront_higher_delta_subset
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (a b Rstar tail : ℝ) (p : ℕ) (ha : 0<a) (hab : a≤b) (hRs : 0<Rstar)
    (hRadius : ∀ y ∈ cylinder, referenceRadius b Rstar p L y<R)
    (hBoundary : ∀ q ∈ nativeSphereFront S L C lam b Rstar p,
      q.2 ∈ frontier cylinder → q ∈ nativeRadialSeedRoom S L C lam R tail) :
    nativeSphereFront S L C lam b Rstar p ⊆
      nativeRadialSeedRoom S L C lam R tail ∪
        (nativeRadialOutsideRoom S L C lam R a Rstar p ∪ nativeSphereFront S L C lam a Rstar p) := by
  intro q hq
  by_cases hSeed : q ∈ nativeRadialSeedRoom S L C lam R tail
  · exact Or.inl hSeed
  right
  have hb : 0<b := ha.trans_le hab
  have hCyl : q.2 ∈ cylinder := by
    obtain ⟨u,hu,hUq⟩ := hq
    have hh : u.1=q.2 := congrArg Prod.snd hUq
    exact hh ▸ hu.1
  have hInterior : q.2 ∈ interior cylinder := by
    by_contra hNo
    have hFront : q.2 ∈ frontier cylinder := by
      change q.2 ∈ closure cylinder ∧ q.2 ∉ interior cylinder
      exact ⟨isClosed_cylinder.closure_eq.symm ▸ hCyl,hNo⟩
    exact hSeed (hBoundary q hq hFront)
  have hLe : referenceRadius a Rstar p L q.2 ≤ referenceRadius b Rstar p L q.2 :=
    referenceRadius_mono_delta a b Rstar p L q.2 ha hab hRs.le
  by_cases hEq : referenceRadius a Rstar p L q.2=referenceRadius b Rstar p L q.2
  · right
    obtain ⟨u,hu,hUq⟩ := hq
    have hh : u.1=q.2 := congrArg Prod.snd hUq
    have hRadii : referenceRadius a Rstar p L u.1=referenceRadius b Rstar p L u.1 := by
      simpa only [hh] using hEq
    refine ⟨u,hu,?_⟩
    change (nativeCoverEndpoint S L C lam ((u.1,referenceRadius a Rstar p L u.1),u.2),u.1)=q
    rw [hRadii]
    exact hUq
  · left
    have hLt : referenceRadius a Rstar p L q.2 < referenceRadius b Rstar p L q.2 :=
      lt_of_le_of_ne hLe hEq
    have hqN := nativeSphereFront_subset_nativeNormalImage S L C lam hlam R hR hRoom
      b Rstar hb hRs p hRadius hq
    have hNorm := nativeVelocityInverse_norm_on_nativeSphereFront S L C lam hlam R hR hRoom
      b Rstar p hb hRs hRadius q hq
    have hNormGt : referenceRadius a Rstar p L q.2 < ‖(nativeVelocityInverse S L C lam R q).2‖ := by
      rw [hNorm]
      exact hLt
    have hSq := (sq_lt_sq₀ (referenceRadius_pos a Rstar p L q.2 ha hRs).le (norm_nonneg _)).mpr hNormGt
    rw [nativeRadialOutsideRoom_eq_positive_nativeGlobalEnergy S L C lam hlam R hR hRoom a Rstar ha hRs p]
    refine ⟨hqN,hInterior,?_⟩
    unfold nativeGlobalEnergy
    rw [real_inner_self_eq_norm_sq]
    nlinarith only [hSq]

/-- Retaining the complete old front makes upward coverage legitimate even on equal-radius pieces. -/
theorem nativeSphereFront_higher_delta_covered
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (a b Rstar tail : ℝ) (p : ℕ) (ha : 0<a) (hab : a≤b) (hRs : 0<Rstar)
    (hRadius : ∀ y ∈ cylinder, referenceRadius b Rstar p L y<R)
    (hBoundary : ∀ q ∈ nativeSphereFront S L C lam b Rstar p,
      q.2 ∈ frontier cylinder → q ∈ nativeRadialSeedRoom S L C lam R tail)
    (U : Set (R3 × R3))
    (hSeed : nativeRadialSeedRoom S L C lam R tail ⊆ U)
    (hOutside : nativeRadialOutsideRoom S L C lam R a Rstar p ⊆ U)
    (hFront : nativeSphereFront S L C lam a Rstar p ⊆ U) :
    nativeSphereFront S L C lam b Rstar p ⊆ U := by
  intro q hq
  rcases nativeSphereFront_higher_delta_subset S L C lam hlam R hR hRoom
    a b Rstar tail p ha hab hRs hRadius hBoundary hq with h | h | h
  · exact hSeed h
  · exact hOutside h
  · exact hFront h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
