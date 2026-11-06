import Calderon.ActualHighAdjointMovingTraceNativeDecomposition
import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.ActualAdjointMovingBoundaryFamilies

/-! Local quotient auxiliary only; radius-uniform estimates require its signed-R2 graph. -/
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

def referenceHighAdjointMovingDifferenceQuotient (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (R y)⁻¹ • (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i -
    ((R y)⁻¹ • sphereHighHarmonicDerivativeTransposeL hF hO hD i + referenceRadiusHorizontalLogDerivative g L q R y i • sphereSobolevShiftedDegreeL (3/2 : ℝ) +
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i)))

def referenceLowerAdjointMovingDifferenceQuotient (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  (R y)⁻¹ • (referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i -
    ((R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i + referenceRadiusHorizontalLogDerivative g L q R y i • sphereSobolevShiftedDegreeL (1/2 : ℝ) +
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i)))

attribute [local irreducible] referenceHighAdjointMovingDifferenceQuotient
  referenceLowerAdjointMovingDifferenceQuotient

lemma referenceAdjointMovingBoundaryActionFamily_differenceQuotient_factorization
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) (hr : R y ≠ 0) :
    (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i = (R y)⁻¹ • sphereHighHarmonicDerivativeTransposeL hF hO hD i + referenceRadiusHorizontalLogDerivative g L q R y i • sphereSobolevShiftedDegreeL (3/2 : ℝ) +
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i) + R y • referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) ∧
    (referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i = (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i + referenceRadiusHorizontalLogDerivative g L q R y i • sphereSobolevShiftedDegreeL (1/2 : ℝ) +
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i) + R y • referenceLowerAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) := by
  have hCancel : R y * (R y)⁻¹ = 1 := mul_inv_cancel₀ hr
  constructor
  · apply ContinuousLinearMap.ext
    intro u
    simp (config := { instances := true }) only
      [referenceHighAdjointMovingDifferenceQuotient,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply,smul_smul,hCancel,one_smul]
    abel
  · apply ContinuousLinearMap.ext
    intro u
    simp (config := { instances := true }) only
      [referenceLowerAdjointMovingDifferenceQuotient,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply,smul_smul,hCancel,one_smul]
    abel


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingDifferenceQuotient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointMovingDifferenceQuotient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMovingBoundaryActionFamily_differenceQuotient_factorization
