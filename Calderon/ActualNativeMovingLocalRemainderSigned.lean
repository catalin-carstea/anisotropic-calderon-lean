import Calderon.ActualNativeMovingLocalRemainder

/-! The signed local remainder theorem. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  NormalCoordinatesFrame

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointMovingBoundaryActionFamily
  referenceLowerAdjointMovingBoundaryActionFamily referenceRadiusHorizontalLogDerivative
  sphereHighHarmonicDerivativeTransposeL sphereSobolevAngularCoordinateTransposeL
  sphereSobolevShiftedDegreeL sphereSobolevInclusionL
  referenceNativeMovingAdjointParametricCorrection

attribute [local irreducible] referenceHighAdjointMovingDifferenceQuotient
  referenceLowerAdjointMovingDifferenceQuotient

lemma referenceHighAdjointMovingDifferenceQuotient_eq_signed_correction
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (i : Fin 3) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hSegment : ∀ t ∈ uIcc (0 : ℝ) (R y), (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i = referenceHighAdjointMovingActualJetNormalizedCorrection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y) (referenceRadiusHorizontalLogDerivative g L q R y i) i hInv := by
  let f := referenceRadiusHorizontalLogDerivative g L q R y i
  let N := referenceHighAdjointMovingActualJetNormalizedCorrection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y) f i hInv
  let Base : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    (R y)⁻¹ • sphereHighHarmonicDerivativeTransposeL hF hO hD i + f • sphereSobolevShiftedDegreeL (3/2 : ℝ) +
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i)
  have hScalar := referenceRadius_mul_horizontalLogDerivative_eq_fderiv g L q R hR y hr i
  have hFirst : referenceHighAdjointMovingFirstCorrection g L hF hO hD q y (R y) f i =
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i := by
    have h := congrArg (fun c : ℝ =>
      (sphereSobolevRadialDriftAdjointL hF hO hD (3/2 : ℝ) (referenceCenterDrift g L q y)).comp
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)) +
      c • sphereSobolevRadialDriftAdjointL hF hO hD (3/2 : ℝ) (referenceCenterDrift g L q y)) hScalar
    simpa (config := { instances := true }) only
      [referenceHighAdjointMovingFirstCorrection,referenceNativeMovingAdjointParametricCorrection,f]
      using h
  have hNative := referenceHighAdjointMovingBoundaryActionFamily_native_decomposition
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq y hy R i hr hInv hSegment
  have hChange := congrArg
    (fun F : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) =>
      (R y)⁻¹ • sphereHighHarmonicDerivativeTransposeL hF hO hD i + f • sphereSobolevShiftedDegreeL (3/2 : ℝ) + (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp F + R y • N) hFirst
  have hC : referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i = Base + R y • N := hNative.trans hChange
  have hDifference := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      (R y)⁻¹ • (T-Base)) hC
  have hSub : Base + R y • N - Base = R y • N := by abel
  have hAlgebra : (R y)⁻¹ • (Base+R y • N-Base) = N :=
    (congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      (R y)⁻¹ • T) hSub).trans (by
        simp (config := { instances := true }) only
          [smul_smul,inv_mul_cancel₀ hr,one_smul])
  simpa (config := { instances := true }) only
    [referenceHighAdjointMovingDifferenceQuotient,Base,N,f]
    using hDifference.trans hAlgebra

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingDifferenceQuotient_eq_signed_correction
