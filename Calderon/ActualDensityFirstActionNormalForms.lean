import Calderon.ActualWeightedHorizontalActions
import Calderon.ActualNativeMovingLocalRemainder

/-! Normal form of the first action, X = D + V + IF + rE. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceHighHorizontalAction referenceLowerHorizontalAction
  referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingBoundaryActionFamily referenceLowerAdjointMovingBoundaryActionFamily
  referenceNativeMovingAdjointParametricCorrection referenceRadiusHorizontalLogDerivative
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  sphereSobolevInclusionL sphereSobolevShiftedDegreeL
  sphereHighHarmonicDerivativeTransposeL sphereSobolevAngularCoordinateTransposeL

lemma referenceHighDensityFirstAction_normal_form
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i : Fin 3) (hr : R y ≠ 0) :
    referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i =
    referenceHighWeightedHorizontalAction g L q R u y i +
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i (u y) +
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,y),fderiv ℝ R y) i (u y)) +
      R y • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i (u y) := by
  have hFactor := (referenceAdjointMovingBoundaryActionFamily_differenceQuotient_factorization
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hr).1
  have hA : sphereHighHarmonicDerivativeTransposeL hF hO hD i =
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i := by
    unfold sphereHighHarmonicDerivativeTransposeL sphereSobolevAngularCoordinateTransposeL
    rfl
  have hValue := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      referenceHighHorizontalAction g L q u y i + T (u y)) hFactor
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, hA] at hValue
  unfold referenceHighDensityFirstAction referenceHighWeightedHorizontalAction
  exact hValue.trans (by abel)

lemma referenceLowerDensityFirstAction_normal_form
    (q : ℝ) (R : R3 → ℝ) (v : R3 → SphereSobolev (1/2 : ℝ))
    (y : R3) (i : Fin 3) (hr : R y ≠ 0) :
    referenceLowerDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i =
    referenceLowerWeightedHorizontalAction g L q R v y i +
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (v y) +
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i (v y)) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i (v y) := by
  have hFactor := (referenceAdjointMovingBoundaryActionFamily_differenceQuotient_factorization
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hr).2
  have hValue := congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      referenceLowerHorizontalAction g L q v y i + T (v y)) hFactor
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply] at hValue
  unfold referenceLowerDensityFirstAction referenceLowerWeightedHorizontalAction
  exact hValue.trans (by abel)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighDensityFirstAction_normal_form
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerDensityFirstAction_normal_form
