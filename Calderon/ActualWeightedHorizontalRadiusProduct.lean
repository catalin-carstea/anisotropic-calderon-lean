import Calderon.ActualWeightedHorizontalActions
import Calderon.ActualNativeLeadingCovariantRadiusCancellation

/-! Before-source: actual-physical-full-allocation-author-oct16-v001/
EXPANSION-radius-weighted-product-v011.md. Original signed radius and frame. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  NormalCoordinatesFrame

attribute [local irreducible] referenceLowerWeightedHorizontalAction
  referenceRadiusHorizontalLogDerivative referenceMetricGramFrame sphereSobolevInclusionL

lemma referenceLowerWeightedHorizontalAction_radius_smul
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (v : R3 → SphereSobolev (1/2 : ℝ)) (y : R3) (i : Fin 3)
    (hr : R y ≠ 0) (hv : DifferentiableAt ℝ v y) :
    referenceLowerWeightedHorizontalAction g L q R (fun x => R x • v x) y i =
      R y • referenceLowerWeightedHorizontalAction g L q R v y i +
        (R y * referenceRadiusHorizontalLogDerivative g L q R y i) •
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (v y) := by
  have hFrame : conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i) =
      referenceMetricGramFrame g L (q,y) i :=
    (congrArg (fun T : R3 →L[ℝ] R3 => T (coordinateVector i))
      (conformalReferenceGramFrameOperatorJoint_eq_frameOperator g L (q,y))).trans
      ((frameOperator_coordinateVector _ i).trans
        (conformalReferenceGramFrame_eq_referenceMetricGramFrame g L q y i))
  have hLog : referenceRadiusHorizontalLogDerivative g L q R y i =
      (R y)⁻¹ * fderiv ℝ R y (referenceMetricGramFrame g L (q,y) i) := by
    unfold referenceRadiusHorizontalLogDerivative
    rw [fderiv_log_radius_apply R hR y _ hr, hFrame]
  have hRadius : fderiv ℝ R y (referenceMetricGramFrame g L (q,y) i) =
      R y * referenceRadiusHorizontalLogDerivative g L q R y i := by
    rw [hLog, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  have hProduct := referenceLowerWeightedHorizontalAction_smul g L q R R v y i
    (hR.differentiable (by simp) y) hv
  rw [hRadius] at hProduct
  exact hProduct

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerWeightedHorizontalAction_radius_smul
