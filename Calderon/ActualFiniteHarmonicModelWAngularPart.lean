import Calderon.ActualFiniteHarmonicModelWPolynomialIdentity
import Calderon.ActualFiniteHarmonicModelWPolynomialMassBounds
import Calderon.ActualFiniteHarmonicModelWeightedYAngularMassBounds
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
  SmoothAngularApplication CoordinateBootstrapJets ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWAngularPartFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWAngularPartFunction
def nativeWAngularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  nativeWeightedYAngularPart hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam)
      (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam) hδ hR+
    nativeWPolynomialPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR

lemma commutator_nativeW_eq_angularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (hA : ScalarCentral hO hD A) :
    ActualModelCommutatorWords.commutator (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) A =
      ActualModelCommutatorWords.commutator (nativeWAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) A := by
  have halg {S : Type} [Ring S] (s t y w d a : S)
      (hs : a*s=s*a) (ht : a*t=t*a) (hd : a*d=d*a) :
      (s+(t+y)+w-d)*a-a*(s+(t+y)+w-d)=(y+w)*a-a*(y+w) := by
    simp only [add_mul,mul_add,sub_mul,mul_sub,hs,ht,hd]
    abel
  rw [nativeW_eq_polynomial_and_density_parts,nativeWeightedY_eq_scalar_add_angular]
  unfold nativeWAngularPart ActualModelCommutatorWords.commutator
  exact halg
    (coreScalar hO hD
      (fun x => adjointZeroCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x)
      (contDiff_modelAdjointZeroCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR))
    (nativeWeightedYScalarPart hO hD g1 hg1 L lam δ R p _
      (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam) hδ hR)
    (nativeWeightedYAngularPart hO hD g1 hg1 L lam δ R p _
      (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam) hδ hR)
    (nativeWPolynomialPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (coreScalar hO hD (normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p)
      (contDiff_normalizedSecondDriftDensityDivergence g1 g2 hg1 hg2 L lam δ R p hδ hR)) A
    (hA _ _).eq
    (commute_nativeWeightedYScalarPart hO hD g1 hg1 L lam δ R p _
      (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam) hδ hR A hA).eq
    (hA _ _).eq

theorem exists_nativeWAngularPart_uniform_quadratic_expansion
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R, ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      
      HasCoreScalarExpansionBound hO hD (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
        (nativeWAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) x (C*eps) := by
  obtain ⟨CY,hCY,hY⟩ := exists_nativeWeightedYAngularPartMass_uniform_smallness g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CP,hCP,hP⟩ := exists_nativeWPolynomialPartMass_uniform_smallness hO hD g1 g2 hg1 hg2 L hL K hK
  refine ⟨CY+CP,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall
  have hy := hY lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall
  have hp0 := hP lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall
  unfold nativeWAngularPart
  have he := hasCoreScalarExpansionBound_add hO hD _ _ _ x _ _
    (hasCoreScalarExpansionBound_linear_to_quadratic hO hD hF _ x _
      (hasCoreScalarExpansionBound_nativeWeightedYAngularPart hO hD hF g1 hg1 L lam δ R p _
        (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam) hδ hR x))
    (hasCoreScalarExpansionBound_nativeWPolynomialPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR x)
  exact hasCoreScalarExpansionBound_mono hO hD _ _ x _ _ he (by nlinarith)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
