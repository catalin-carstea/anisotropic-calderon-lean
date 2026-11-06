import Calderon.MixedKernelConstruction.MixedKernelNativeRadialSeedCompatibility
import Calderon.MixedKernelConstruction.MixedKernelNativeFrontDeltaOrder
import Calderon.MixedKernelConstruction.MixedKernelNativeOutsideDeltaLimit
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- The original normal image with exactly its zero inverse velocity removed. -/
def nativeNonzeroNormalImage (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R : ℝ) : Set (R3 × R3) :=
  nativeNormalImage S L C lam R ∩ {q | (nativeVelocityInverse S L C lam R q).2≠0}

/-- Internal reached-level property: actual open collar, entire zero front, both PDEs, SAME seed, BOTH full crosses. -/
def NativeReachedAt (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R Rstar tail : ℝ) (p : ℕ) (Hseed : R3 × R3 → ℝ) (a : ℝ) : Prop :=
  ∃ (U : Set (R3 × R3)) (H : R3 × R3 → ℝ), IsOpen U ∧ U ⊆ nativeNonzeroNormalImage S L C lam R ∧
    nativeRadialSeedRoom S L C lam R tail ⊆ U ∧
    nativeRadialOutsideRoom S L C lam R a Rstar p ⊆ U ∧ nativeSphereFront S L C lam a Rstar p ⊆ U ∧
    ProductSolutionOn S L lam H U ∧ EqOn H Hseed (nativeRadialSeedRoom S L C lam R tail) ∧
    (∀ q ∈ U, lam • q.2 ∈ S.W → H q=dilatedKernel1 S lam q) ∧
    (∀ q ∈ U, lam • q.1 ∈ S.W → H q=dilatedKernel2 S lam q)

/-- Every genuine reached witness restricts to its actual canonical domain, retaining the SAME seed and full crosses. -/
theorem native_reached_canonical_solution
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R Rstar tail : ℝ) (p : ℕ) (Hseed : R3 × R3 → ℝ) (a : ℝ)
    (h : NativeReachedAt S L C lam R Rstar tail p Hseed a) :
    ∃ H : R3 × R3 → ℝ, ProductSolutionOn S L lam H (nativeRadialCanonicalRoom S L C lam R a Rstar tail p) ∧
      EqOn H Hseed (nativeRadialSeedRoom S L C lam R tail) ∧
      (∀ q ∈ nativeRadialCanonicalRoom S L C lam R a Rstar tail p,
        lam • q.2 ∈ S.W → H q=dilatedKernel1 S lam q) ∧
      (∀ q ∈ nativeRadialCanonicalRoom S L C lam R a Rstar tail p,
        lam • q.1 ∈ S.W → H q=dilatedKernel2 S lam q) := by
  obtain ⟨U,H,hU,hSource,hSeed,hOutside,hFront,hSol,hEq,h1,h2⟩ := h
  have hSub : nativeRadialCanonicalRoom S L C lam R a Rstar tail p ⊆ U := by
    intro q hq
    rcases hq with hs | ho
    · exact hSeed hs
    · exact hOutside ho
  exact ⟨H,productSolutionOn_mono hSol hSub,hEq,
    fun q hq => h1 q (hSub hq),fun q hq => h2 q (hSub hq)⟩

/-- The SAME actual open kernel reaches every larger original delta, including equal-radius portions of the whole front. -/
theorem native_reached_mono_delta
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (a b Rstar tail : ℝ) (p : ℕ) (ha : 0<a) (hab : a≤b) (hRs : 0<Rstar)
    (Hseed : R3 × R3 → ℝ)
    (hRadius : ∀ y ∈ cylinder, referenceRadius b Rstar p L y<R)
    (hBoundary : ∀ q ∈ nativeSphereFront S L C lam b Rstar p,
      q.2 ∈ frontier cylinder → q ∈ nativeRadialSeedRoom S L C lam R tail)
    (h : NativeReachedAt S L C lam R Rstar tail p Hseed a) :
    NativeReachedAt S L C lam R Rstar tail p Hseed b := by
  obtain ⟨U,H,hU,hSource,hSeed,hOutside,hFront,hSol,hEq,h1,h2⟩ := h
  have hOutsideB : nativeRadialOutsideRoom S L C lam R b Rstar p ⊆ U :=
    (nativeRadialOutsideRoom_mono_delta S L C lam R a b Rstar p ha hab hRs.le).trans hOutside
  have hFrontB : nativeSphereFront S L C lam b Rstar p ⊆ U :=
    nativeSphereFront_higher_delta_covered S L C lam hlam R hR hRoom a b Rstar tail p ha hab hRs
      hRadius hBoundary U hSeed hOutside hFront
  exact ⟨U,H,hU,hSource,hSeed,hOutsideB,hFrontB,hSol,hEq,h1,h2⟩

/-- The GENUINE fixed seed reaches the actual top level; no independent old-side solver is assumed. -/
theorem native_reached_one
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (Rstar tail : ℝ) (p : ℕ) (hRs : 0<Rstar)
    (hRadius : ∀ y ∈ cylinder, referenceRadius 1 Rstar p L y<R)
    (hTail : ∀ y ∈ cylinder, tail<referenceRadius 1 Rstar p L y)
    (Hseed : R3 × R3 → ℝ)
    (hSeedSol : ProductSolutionOn S L lam Hseed (nativeRadialSeedRoom S L C lam R tail))
    (hSeed1 : ∀ q ∈ nativeRadialSeedRoom S L C lam R tail,
      lam • q.2 ∈ S.W → Hseed q=dilatedKernel1 S lam q)
    (hSeed2 : ∀ q ∈ nativeRadialSeedRoom S L C lam R tail,
      lam • q.1 ∈ S.W → Hseed q=dilatedKernel2 S lam q) :
    NativeReachedAt S L C lam R Rstar tail p Hseed 1 := by
  have hSource : nativeRadialSeedRoom S L C lam R tail ⊆ nativeNonzeroNormalImage S L C lam R :=
    fun q hq => ⟨hq.1,hq.2.1⟩
  have hFront : nativeSphereFront S L C lam 1 Rstar p ⊆ nativeRadialSeedRoom S L C lam R tail := by
    intro q hq
    have hqN := nativeSphereFront_subset_nativeNormalImage S L C lam hlam R hR hRoom
      1 Rstar (by norm_num) hRs p hRadius hq
    have hNorm := nativeVelocityInverse_norm_on_nativeSphereFront S L C lam hlam R hR hRoom
      1 Rstar p (by norm_num) hRs hRadius q hq
    have hCyl : q.2 ∈ cylinder := by
      obtain ⟨u,hu,hUq⟩ := hq
      have hh : u.1=q.2 := congrArg Prod.snd hUq
      exact hh ▸ hu.1
    have hv : (nativeVelocityInverse S L C lam R q).2≠0 := by
      apply norm_pos_iff.mp
      rw [hNorm]
      exact referenceRadius_pos 1 Rstar p L q.2 (by norm_num) hRs
    refine ⟨hqN,hv,Or.inr ?_⟩
    rw [hNorm]
    exact hTail q.2 hCyl
  refine ⟨nativeRadialSeedRoom S L C lam R tail,Hseed,
    isOpen_nativeRadialSeedRoom S L C lam hlam R hR hRoom tail,hSource,subset_rfl,
    nativeRadialOutsideRoom_one_subset_nativeRadialSeedRoom S L C lam hlam R hR hRoom Rstar tail p hRs hTail,
    hFront,hSeedSol,?_,hSeed1,hSeed2⟩
  intro q hq
  rfl

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
