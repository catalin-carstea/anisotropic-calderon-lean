import Calderon.ActualFiniteHarmonicModelReferenceWeightedYRaw
import Calderon.ActualFiniteHarmonicModelReferenceTraceZeroAdjointExpansion
import Calderon.ActualFiniteHarmonicModelDriftConnectionExpansion
import Calderon.ActualFiniteHarmonicModelReferenceTraceZeroRaw
import Calderon.ActualFiniteHarmonicModelDriftZeroRaw

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualNormalizedSphereRotation ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDSpectralTransport ActualReferenceDDHigherSpectralGraphs
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondModelDefectCoefficients
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ActualScalarPrincipalAdjoint NaturalAngularAdjoint ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftNativeAdjunction ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftWeightedCoefficients ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothMetricFrame MovingFrameConnection SmoothSphereFields
  SmoothAngularApplication
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWPolynomialFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWPolynomialFunction
def nativeWPolynomialPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h :=
    ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hhentry (i j : Fin 3) : ContDiff ℝ ∞ (fun y => h y i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hh
  exact
    (nativeReferenceTraceZeroAdjointRawAction hO hD g1 hg1 L lam δ R p h hh hδ hR-
      nativeReferenceTraceZeroRawAction hO hD g1 hg1 L lam δ R p h hh hδ hR) +
    (∑ a : Fin 3, coreScalar hO hD (physicalMixedDensityCorrection g1 L lam h a)
      (contDiff_physicalMixedDensityCorrection g1 hg1 L lam h hhentry a)*coreDerivative hO hD hF a) +
    (∑ a : Fin 3, coreScalar hO hD (physicalMixedProfileCoefficient g1 L lam δ R p h a)
      (contDiff_physicalMixedProfileCoefficient g1 hg1 L lam δ R p h hδ hR hhentry a)*
      (coreDerivative hO hD hF a*(coreDegree hO hD-1)-coreRaising hO hD hF a*coreDegree hO hD)) +
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      coreScalar hO hD (physicalMixedConnectionCoefficient g1 L lam h a b c)
      (contDiff_physicalMixedConnectionCoefficient g1 hg1 L lam h hhentry a b c)*
      (-(coreRotation hO hD b c*coreDerivative hO hD hF a)-coreRaising hO hD hF a*coreRotation hO hD b c)) +
    (∑ a : Fin 3, ∑ b : Fin 3, coreScalar hO hD (physicalPureAngularCoefficient g1 L lam δ R p h a b)
      (contDiff_physicalPureAngularCoefficient g1 hg1 L lam δ R p h hδ hR hhentry a b)*
      (coreDerivative hO hD hF b*coreDerivative hO hD hF a-coreRaising hO hD hF a*coreRaising hO hD hF b)) +
    (-2 : ℝ) • nativeDriftConnectionRawAction hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR

def nativeWPolynomialPartMass (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (x : R3) : ℝ :=
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  (nativeReferenceTraceZeroRawMass g1 L lam δ R p h x+nativeReferenceTraceZeroRawMass g1 L lam δ R p h x)+
    (∑ a : Fin 3, |physicalMixedDensityCorrection g1 L lam h a x|)+
    (∑ a : Fin 3, |physicalMixedProfileCoefficient g1 L lam δ R p h a x| *3)+
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, |physicalMixedConnectionCoefficient g1 L lam h a b c x| *2)+
    (∑ a : Fin 3, ∑ b : Fin 3, |physicalPureAngularCoefficient g1 L lam δ R p h a b x| *2)+
    2*nativeDriftZeroRawMass g1 g2 L lam δ R p x

lemma hasCoreScalarExpansionBound_nativeWPolynomialPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
      (nativeWPolynomialPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) x
      (nativeWPolynomialPartMass g1 g2 L lam δ R p x) := by
  let T := fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
    coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2
  have hprod (i j : CoreAngularGeneratorIndex) :
      HasCoreScalarExpansionBound hO hD T (coreAngularGenerator hO hD hF i*coreAngularGenerator hO hD hF j) x 1 := by
    simpa only [one_mul] using hasCoreScalarExpansionBound_product hO hD
      (coreAngularGenerator hO hD hF) (coreAngularGenerator hO hD hF)
      (scalarCentral_coreAngularGenerator hO hD hF) _ _ x 1 1
      (hasCoreScalarExpansionBound_generator hO hD hF i x)
      (hasCoreScalarExpansionBound_generator hO hD hF j x)
  have hlin (i : CoreAngularGeneratorIndex) :
      HasCoreScalarExpansionBound hO hD T (coreAngularGenerator hO hD hF i) x 1 :=
    hasCoreScalarExpansionBound_linear_to_quadratic hO hD hF _ x 1
      (hasCoreScalarExpansionBound_generator hO hD hF i x)
  unfold nativeWPolynomialPart nativeWPolynomialPartMass
  dsimp only
  apply hasCoreScalarExpansionBound_add hO hD
  · apply hasCoreScalarExpansionBound_add hO hD
    · apply hasCoreScalarExpansionBound_add hO hD
      · apply hasCoreScalarExpansionBound_add hO hD
        · apply hasCoreScalarExpansionBound_add hO hD
          · exact hasCoreScalarExpansionBound_sub hO hD _ _ _ x _ _
              (hasCoreScalarExpansionBound_nativeReferenceTraceZeroAdjointRawAction hO hD hF g1 hg1 L lam δ R p _ _ hδ hR x)
              (hasCoreScalarExpansionBound_nativeReferenceTraceZeroRawAction hO hD hF g1 hg1 L lam δ R p _ _ hδ hR x)
          · apply hasCoreScalarExpansionBound_sum hO hD
            intro a _
            rw [← mul_one |physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a x|]
            apply hasCoreScalarExpansionBound_scalar_mul hO hD
            simpa only [T,coreAngularGenerator] using hlin (Sum.inl a)
        · apply hasCoreScalarExpansionBound_sum hO hD
          intro a _
          apply hasCoreScalarExpansionBound_scalar_mul hO hD
          have hd := hasCoreScalarExpansionBound_sub hO hD T _ _ x 1 1
            (hprod (Sum.inl a) (Sum.inr (Sum.inr (Sum.inr true)))) (hlin (Sum.inl a))
          have hr := hprod (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr (Sum.inr true)))
          have ha {S : Type} [Ring S] (D N : S) : D*(N-1)=D*N-D := by noncomm_ring
          rw [ha (coreDerivative hO hD hF a) (coreDegree hO hD)]
          have ht := hasCoreScalarExpansionBound_sub hO hD T _ _ x (1+1) 1 hd hr
          simpa only [T,coreAngularGenerator,show (1+1+1 : ℝ)=3 by norm_num] using ht
      · apply hasCoreScalarExpansionBound_sum hO hD
        intro a _
        apply hasCoreScalarExpansionBound_sum hO hD
        intro b _
        apply hasCoreScalarExpansionBound_sum hO hD
        intro c _
        apply hasCoreScalarExpansionBound_scalar_mul hO hD
        have ht := hasCoreScalarExpansionBound_sub hO hD T _ _ x 1 1
          (hasCoreScalarExpansionBound_neg hO hD T _ x 1 (hprod (Sum.inr (Sum.inr (Sum.inl (b,c)))) (Sum.inl a)))
          (hprod (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr (Sum.inl (b,c)))))
        simpa only [T,coreAngularGenerator,show (1+1 : ℝ)=2 by norm_num] using ht
    · apply hasCoreScalarExpansionBound_sum hO hD
      intro a _
      apply hasCoreScalarExpansionBound_sum hO hD
      intro b _
      apply hasCoreScalarExpansionBound_scalar_mul hO hD
      have ht := hasCoreScalarExpansionBound_sub hO hD T _ _ x 1 1
        (hprod (Sum.inl b) (Sum.inl a)) (hprod (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)))
      simpa only [T,coreAngularGenerator,show (1+1 : ℝ)=2 by norm_num] using ht
  · have ht := hasCoreScalarExpansionBound_smul hO hD T _ x _ (-2)
      (hasCoreScalarExpansionBound_linear_to_quadratic hO hD hF _ x _
        (hasCoreScalarExpansionBound_nativeDriftConnectionRawAction hO hD hF g1 g2 hg1 hg2 L lam δ R p hδ hR x))
    norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht
    simpa only [T] using ht

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
