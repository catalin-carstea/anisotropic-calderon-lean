import Calderon.ActualPhysicalDensityProductsAdjointOperatorCore
import Calderon.ActualPhysicalDensityProductsWeightedAdjunction
import Calderon.FiniteOperatorProductsSmoothness
import Calderon.ActualPhysicalDensityProductsOperatorIdentities
import Calderon.PhysicalDensityProductsWeightedSumsSmoothness
import Calderon.PhysicalDensityProductsConcreteWeightedSums
import Calderon.PhysicalDensityProductsPredicateTransport

/-! Actual Main M1 Products adjoint. Full nine-root before-code expansion and
exact original definitions were reviewed before authoring. No quantitative
Productsdag cap, finite-output assumption or intrinsic Half adjoint is used. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceAdjointMovingDifferenceQuotientPivotHigh referenceAdjointMovingDifferenceQuotientPivotLow

set_option Elab.async false

lemma contDiffOn_referencePhysicalDensityProducts_half_operators
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) :
    let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let U : Set R3 := {y | R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈ Ω) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)}
    ContDiffOn ℝ ∞ (fun y : R3 => referencePhysicalDensityProductsHalfOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y) U ∧
    ContDiffOn ℝ ∞ (fun y : R3 => referencePhysicalDensityProductsAdjointHalfOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y) U :=
  referencePhysicalDensityProducts_half_operators_predicate
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
    (fun F : R3 → Hi →L[ℝ] Half => ContDiffOn ℝ ∞ F
      {y | R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)})
    (contDiffOn_referencePhysicalDensityProducts_weighted_sums
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg g2 hg2 q hq R hR)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
