import Calderon.ActualReferenceSameBoundaryCorrection
import Calderon.ActualHighMovingBoundaryAction

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
MOVING-NATIVE-TRACE-IDENTIFICATION-EXPANSION-v001.md. Same actual C and bulk trace. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHarmonicLiftFamily referenceNativeMovingRadiusTraceOperator
  referenceNativeCenterTraceOperator referenceNativeJacobiTraceCorrection
  referenceNativeCoordinateTraceOperatorFamily referenceNativeRadialTraceOperatorFamily
  referenceHighMovingBoundaryAction referenceJacobiSphereCoefficient

theorem referenceNativeMovingRadiusTraceOperator_eq_on_nativeThreeHalfTrace
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (E : BallSobolev 2) :
    referenceNativeMovingRadiusTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q R y i hInv E =
    referenceNativeMovingRadiusTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q R y i hInv
      (harmonicLiftCompletion hF (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 E)) := by
  have hCorrection := referenceHarmonicLiftFamily_eq_harmonicLiftCompletion_nativeThreeHalfTrace
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel q (y,R y) hStrong hWeak E
  have hPost := congrArg (fun U : BallSobolev 2 =>
    (R y)⁻¹ • strongCoordinateTraceL hcalc τ0 i U +
      R y • ∑ j : Fin 3,
        sphereContinuousScalarMulL
          (referenceJacobiSphereCoefficient g hg L y0 Φ B ε C ρ H a w hData q y (R y) i j hInv)
          (strongCoordinateTraceL hcalc τ0 j U) +
      referenceRadiusHorizontalLogDerivative g L q R y i • outwardRadialTraceL hcalc τ0 U)
    hCorrection
  simpa only [referenceNativeMovingRadiusTraceOperator, referenceNativeCenterTraceOperator,
    referenceNativeJacobiTraceCorrection, referenceNativeCoordinateTraceOperatorFamily,
    referenceNativeRadialTraceOperatorFamily, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply] using hPost

theorem referenceHighMovingBoundaryAction_nativeThreeHalfTrace_eq_coarse
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (E : BallSobolev 2) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        q R y i hInv (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 E)) =
    sphereSobolevZeroEquiv hO hD
      (referenceNativeMovingRadiusTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q R y i hInv E) := by
  have hBoundary := referenceHighMovingBoundaryAction_eq_coarse_moving
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv
      hNormal hStrong hWeak (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 E)
  have hNative := referenceNativeMovingRadiusTraceOperator_eq_on_nativeThreeHalfTrace
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hKernel q R y i hInv hStrong hWeak E
  exact hBoundary.trans (congrArg (sphereSobolevZeroEquiv hO hD) hNative.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingRadiusTraceOperator_eq_on_nativeThreeHalfTrace
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighMovingBoundaryAction_nativeThreeHalfTrace_eq_coarse
