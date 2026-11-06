import Calderon.ActualNativeOutputCompression
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  WeightedAngularConvergence WeightedBaseSpectral ReferenceDensityBounds ActualFiniteHarmonicCore
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevPartialSumL finiteCoreSobolevLift
  harmonicSphereSubspace nativePacketPhysicalDensityOperator

/-- A conditional finite-input/finite-output estimate for the literal angular
compression of the ORIGINAL native physical operator. Its same c works for
all sufficiently large angular cutoffs. This definition asserts no estimate. -/
def NativeFinitePhysicalCompressionCoreBound
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics)
    (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData)
    (L:ℝ) (cover:NativeNormalCover S L) (chi:R3→ℝ) (q delta Rstar:ℝ)
    (p:ℕ) (c:ℝ) (n0:ℕ):Prop :=
  ∀ n:ℕ,max 1 n0 ≤ n →
  ∀ A:smoothCompactFiniteSphereCore hO hD,
    finiteHarmonicBand hO hD n (A:R3→SphereL2) → tsupport (A:R3→SphereL2)⊆tsupport chi →
    (∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) →
  ∀ B:smoothCompactFiniteSphereCore hO hD,
    finiteHarmonicBand hO hD n (B:R3→SphereL2) → tsupport (B:R3→SphereL2)⊆tsupport chi →
    (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD ((B:R3→SphereL2) y))=
      sphereSobolevPartialSumL (-(1/2:ℝ)) n
        (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y)) →
    c*(∫ y,referenceDensityFamily S.g1 L (q,y)*‖(A:R3→SphereL2) y‖^2) ≤
      ∫ y,referenceDensityFamily S.g1 L (q,y)*‖(B:R3→SphereL2) y‖^2

/-- No finite angular support is imposed on the full genuine output V.
Project it at one global input-band cutoff, then use the original weighted
projection contraction. The same c is preserved. -/
theorem nativeFinitePhysicalCoerciveBound_of_compression_core_bound
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics)
    (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData)
    (L:ℝ) (cover:NativeNormalCover S L) (chi:R3→ℝ) (q delta Rstar:ℝ)
    (p:ℕ) (c:ℝ) (n0:ℕ)
    (hC:NativeFinitePhysicalCompressionCoreBound hcalc hF hO hD tau0 S L cover chi q delta Rstar p c n0):
    NativeFinitePhysicalCoerciveBound hcalc hF hO hD tau0 S L cover chi q delta Rstar p c := by
  intro A hASupp hMean V hV hVc hVSupp hGraph
  obtain ⟨m,hm⟩ := A.property.2.2
  let n:ℕ := max m (max 1 n0)
  have hn:max 1 n0 ≤ n := le_max_right _ _
  have hBandA:finiteHarmonicBand hO hD n (A:R3→SphereL2) := by
    intro y k hk
    exact hm y k ((le_max_left _ _).trans hk)
  let B:smoothCompactFiniteSphereCore hO hD := nativePhysicalOutputPartialSumCore hO hD n V hV hVc
  have hBandB:finiteHarmonicBand hO hD n (B:R3→SphereL2) := by
    intro y k hk
    change sphereHarmonicCoordinate hO hD k (sphereHarmonicPartialSum hO hD n (V y))=0
    rw [sphereHarmonicCoordinate_partialSum,ite_eq_right (not_lt.mpr hk)]
  have hBSupp:tsupport (B:R3→SphereL2)⊆tsupport chi :=
    (tsupport_nativePhysicalOutputPartialSumCore_subset hO hD n V hV hVc).trans hVSupp
  have hBGraph:∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD ((B:R3→SphereL2) y))=
      sphereSobolevPartialSumL (-(1/2:ℝ)) n
        (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y) := by
    intro i y hy
    exact negative_sobolev_graph_of_sphereHarmonicPartialSum hO hD n (V y) _ (hGraph i y hy)
  have hBound:=hC n hn A hBandA hASupp hMean B hBandB hBSupp hBGraph
  exact hBound.trans (integral_referenceDensity_partialSum_norm_sq_le S.g1 S.g1_admissible
    L q hO hD n V hV.continuous hVc)

theorem nativeFinitePhysicalCoerciveBound_of_eventual_compression_core_bound
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics)
    (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData)
    (L:ℝ) (cover:NativeNormalCover S L) (chi:R3→ℝ) (q delta Rstar:ℝ)
    (p:ℕ) (c:ℝ)
    (hC:∃ n0:ℕ,NativeFinitePhysicalCompressionCoreBound hcalc hF hO hD tau0 S L cover chi q delta Rstar p c n0):
    NativeFinitePhysicalCoerciveBound hcalc hF hO hD tau0 S L cover chi q delta Rstar p c := by
  obtain ⟨n0,h⟩ := hC
  exact nativeFinitePhysicalCoerciveBound_of_compression_core_bound hcalc hF hO hD tau0 S L cover
    chi q delta Rstar p c n0 h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
