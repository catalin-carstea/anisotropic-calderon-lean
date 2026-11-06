import Calderon.ActualReferenceTwoAngleTangentialAdjointEndpointFamilies
import Calderon.ActualReferenceTwoAngleTangentBoundaryCoefficients
import Calderon.SphereSobolevTangentialDerivative
import Calderon.NativeNegativeHalfCoefficientCoordinateProduct
import Calderon.NativeHalfCoefficientRotationDualAdjunction
import Calderon.SphereSobolevCoordinateNegativeHalfOrder
/-! Actual native tangent adjunction. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeBoundaryCoefficientFamilies NativeCoefficientBoundaryMultiplier
  NativeNegativeHalfCoefficientCoordinateProduct
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) (iA jA kA lA : Fin 3)

lemma smoothSphereValue_referenceTwoAngleTangentRotationJetsFamily_product (i j : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    smoothSphereValue (coefficientSmoothData
      (referenceTwoAngleTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 i j t)) =
    smoothSphereValue (coefficientSmoothData
      (referenceTwoAngleTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA i t)) * sphereCoordinate j := by
  ext x
  have hg := coefficientValue_commonSupportCoefficientFamily 2 (tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA) i j)
    (contDiff_tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (tangentRotationCoefficientFunction_support (referenceTwoAnglePrincipalFamily a iA jA kA lA) (closedBall (0 : R3) 3)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 i j) t (x : R3)
  have hq := coefficientValue_commonSupportCoefficientFamily 2 (tangentCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA) i)
    (contDiff_tangentCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 i)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (tangentCoefficientFunction_support (referenceTwoAnglePrincipalFamily a iA jA kA lA) (closedBall (0 : R3) 3)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 i) t (x : R3)
  change coefficientValue 2 (referenceTwoAngleTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 i j t) (x : R3) =
    coefficientValue 2 (referenceTwoAngleTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA i t) (x : R3) * (x : R3) j
  exact hg.trans (congrArg (fun r : ℝ => r * (x : R3) j) hq.symm)

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceTwoAngleTangentialHalfRotationFamily (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceTwoAngleTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 i j t)).comp
        (sphereSobolevRotationL (1/2:ℝ) j i)

lemma referenceTwoAngleTangentialLowerFamily_eq_rotation (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    (∑ i : Fin 3, (referenceTwoAngleTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA kA lA i t).comp
      (sphereTangentialDerivativeL hF hO hD i)) =
    referenceTwoAngleTangentialHalfRotationFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t := by
  apply ContinuousLinearMap.ext
  intro u
  unfold referenceTwoAngleTangentialHalfRotationFamily sphereTangentialDerivativeL
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hPoint := congrArg
    (fun T : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      T (sphereSobolevRotationL (1/2:ℝ) j i u))
    (nativeNegativeHalfCoefficientMulL_coordinate_comp_eq hcalc hF hO hD τ0
      (referenceTwoAngleTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA i t)
      (referenceTwoAngleTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 i j t) j
      (smoothSphereValue_referenceTwoAngleTangentRotationJetsFamily_product g L y0 Φ B ε C ρ H a w hData iA jA kA lA i j t))
  have hProduct : (referenceTwoAngleTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA kA lA i t)
      (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2:ℝ)) (EuclideanSpace.single j 1)
        (sphereSobolevRotationL (1/2:ℝ) j i u)) =
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceTwoAngleTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 i j t)
      (sphereSobolevRotationL (1/2:ℝ) j i u) := by
    simpa only [ContinuousLinearMap.comp_apply, referenceTwoAngleTangentBoundaryMultiplierFamily] using hPoint
  have hOrderPoint := congrArg
    (fun T : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      T (sphereSobolevRotationL (1/2:ℝ) j i u))
    (sphereSobolevLinearCoordinateMulL_negative_half_notation_eq hF hO hD (EuclideanSpace.single j 1))
  exact (congrArg
    (referenceTwoAngleTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA kA lA i t)
    hOrderPoint).trans hProduct

lemma sphereSobolevDualPairing_referenceTwoAngleTangentialHalfRotation_adjoint
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) v
      (referenceTwoAngleTangentialHalfRotationFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t u) =
    sphereSobolevDualPairing (1/2:ℝ) u
      (referenceTwoAngleTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t v) := by
  unfold referenceTwoAngleTangentialHalfRotationFamily referenceTwoAngleTangentialAdjointHalfFamily
  simp only [ContinuousLinearMap.sum_apply,sphereSobolevDualPairing,inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact sphereSobolevDualPairing_nativeHalfCoefficientRotation_adjoint hcalc hF hO hD τ0
    (referenceTwoAngleTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 i j t) j i u v

lemma sphereSobolevDualPairing_referenceTwoAngleTangentialLower_adjoint
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) v
      ((∑ i : Fin 3, (referenceTwoAngleTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA kA lA i t).comp
        (sphereTangentialDerivativeL hF hO hD i)) u) =
    sphereSobolevDualPairing (1/2:ℝ) u
      (referenceTwoAngleTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t v) :=
  (congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevDualPairing (1/2:ℝ) v (T u))
      (referenceTwoAngleTangentialLowerFamily_eq_rotation g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t)).trans
    (sphereSobolevDualPairing_referenceTwoAngleTangentialHalfRotation_adjoint g L y0 Φ B ε C ρ H a w hData iA jA kA lA
      hcalc hF hO hD τ0 t u v)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothSphereValue_referenceTwoAngleTangentRotationJetsFamily_product
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleTangentialHalfRotationFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleTangentialLowerFamily_eq_rotation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTwoAngleTangentialHalfRotation_adjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTwoAngleTangentialLower_adjoint
