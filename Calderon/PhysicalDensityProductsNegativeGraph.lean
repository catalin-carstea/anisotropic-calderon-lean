import Calderon.ActualPhysicalDensityProductsAdjointOperatorCore

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

lemma referencePhysicalDensityProductsHalfOperator_negative_graph_of_eq_zero_off
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (K : Set R3) (hKgeom : K ⊆ closedBall y0 ρ)
    (hRoom : ∀ y ∈ K, R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible))
    (u : R3 → Hi) (hu : ∀ y : R3, y ∉ K → u y = 0) :
    ∀ y : R3,
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referencePhysicalDensityProductsHalfOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y (u y)) =
(R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
          (referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j (u y))) +
       referenceLowerAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) j (u y))))) := by
  classical
  intro y
  by_cases hy : y ∈ K
  · have hyNorm : ‖y-y0‖ ≤ ρ := by
      simpa only [mem_closedBall,dist_eq_norm] using hKgeom hy
    have hRoomY := hRoom y hy
    exact referencePhysicalDensityProductsHalfOperator_negative_inclusion
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 q hq R hR y
        hyNorm hRoomY.1 hRoomY.2.2 hRoomY.2.1 (u y)
  · simp only [hu y hy,map_zero,add_zero,smul_zero,Finset.sum_const_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
