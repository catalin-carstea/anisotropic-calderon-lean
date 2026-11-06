import Calderon.ActualPhysicalDensityHigherFirstSectionDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceHighHorizontalAction referenceMetricGramFrame referenceHighHorizontalAngularL
  referenceHighAdjointMovingBoundaryActionFamily sphereSobolevInclusionL
  referencePhysicalDensityOperator referenceDensityCovariantSecondAction
  referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint

theorem referenceHighDensityFirstAction_eventuallyEq
    (q : ℝ) (R : R3 → ℝ) (u v : R3 → SphereSobolev (3/2:ℝ))
    (y : R3) (j : Fin 3) (h : u =ᶠ[𝓝 y] v) :
    (fun z => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u z j) =ᶠ[𝓝 y]
    (fun z => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v z j) := by
  filter_upwards [h,h.fderiv (𝕜 := ℝ)] with z hz hd
  simp only [referenceHighDensityFirstAction,referenceHighHorizontalAction,hz,hd]

theorem referencePhysicalDensityOperator_congr_of_eventuallyEq
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u v : R3 → SphereSobolev (3/2:ℝ)) (y : R3) (h : u =ᶠ[𝓝 y] v) :
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y := by
  have hFirst (j : Fin 3) := referenceHighDensityFirstAction_eventuallyEq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u v y j h
  have hPoint (j : Fin 3) := (hFirst j).self_of_nhds
  have hOrdered (i j : Fin 3) := referenceLowerDensityFirstAction_congr_of_eventuallyEq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun z => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u z j)
      (fun z => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v z j) y i (hFirst j)
  simp only [referencePhysicalDensityOperator,referenceDensityCovariantSecondAction,hOrdered,hPoint]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
