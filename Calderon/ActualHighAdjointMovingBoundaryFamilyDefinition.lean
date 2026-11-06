import Calderon.ActualHighAdjointJacobiBoundaryFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceJacobiBoundaryCoefficientJets
  referenceJacobiBoundaryThreeHalfCoefficientJets referenceHighAdjointCoordinateBoundaryFamily
  referenceLowerAdjointCoordinateBoundaryFamily nativeThreeHalfCoefficientMulL
  referenceJacobiBoundaryThreeHalfCoefficientFamily
  referenceLowerMovingBoundaryActionFamily referenceLowerMovingBoundaryAction
  referenceHighAdjointJacobiBoundaryCorrection referenceHighAdjointMovingBoundaryAction

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hg : IsAdmissibleMetric g)

def referenceHighAdjointMovingBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (R t.2)⁻¹ • referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i +
  R t.2 • referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i +
  referenceRadiusHorizontalLogDerivative g L t.1 R t.2 i •
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2))

theorem referenceHighAdjointMovingBoundaryActionFamily_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,((t.2,R t.2),x.val))).IsInvertible) :
    referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R t i =
    referenceHighAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t.1 R t.2 i hInv := by
  have hJ := referenceHighAdjointJacobiBoundaryCorrectionFamily_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i hInv
  have hCombined := congrArg (fun J : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
    (R t.2)⁻¹ • referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i +
      R t.2 • J + referenceRadiusHorizontalLogDerivative g L t.1 R t.2 i •
        referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2))) hJ
  simpa only [referenceHighAdjointMovingBoundaryActionFamily,referenceHighAdjointMovingBoundaryAction]
    using hCombined

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingBoundaryActionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingBoundaryActionFamily_eq
