import Calderon.ActualReferenceTangentialAdjointEndpointFamilies
import Calderon.ActualReferenceBoundaryCoefficientFamilies
import Calderon.SphereSobolevTangentialDerivative
import Calderon.NativeNegativeHalfCoefficientCoordinateProduct
import Calderon.NativeHalfCoefficientRotationDualAdjunction
import Calderon.SphereSobolevCoordinateNegativeHalfOrder
set_option autoImplicit false
set_option maxSynthPendingDepth 10
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
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma smoothSphereValue_referenceTangentRotationJetsFamily_product (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    smoothSphereValue (coefficientSmoothData
      (referenceTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j p)) =
    smoothSphereValue (coefficientSmoothData
      (referenceTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i p)) * sphereCoordinate j := by
  ext x
  have hg := coefficientValue_commonSupportCoefficientFamily 2 (tangentRotationCoefficientFunction a i j)
    (contDiff_tangentRotationCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j) p (x : R3)
  have hq := coefficientValue_commonSupportCoefficientFamily 2 (tangentCoefficientFunction a i)
    (contDiff_tangentCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (tangentCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i) p (x : R3)
  change coefficientValue 2 (referenceTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j p) (x : R3) =
    coefficientValue 2 (referenceTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i p) (x : R3) * (x : R3) j
  exact hg.trans (congrArg (fun r : ℝ => r * (x : R3) j) hq.symm)

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceTangentialHalfRotationFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j p)).comp
        (sphereSobolevRotationL (1/2:ℝ) j i)

lemma referenceTangentialLowerFamily_eq_rotation (p : ℝ × (R3 × ℝ)) :
    (∑ i : Fin 3, (referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i p).comp
      (sphereTangentialDerivativeL hF hO hD i)) =
    referenceTangentialHalfRotationFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p := by
  apply ContinuousLinearMap.ext
  intro u
  unfold referenceTangentialHalfRotationFamily sphereTangentialDerivativeL
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hPoint := congrArg
    (fun T : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      T (sphereSobolevRotationL (1/2:ℝ) j i u))
    (nativeNegativeHalfCoefficientMulL_coordinate_comp_eq hcalc hF hO hD τ0
      (referenceTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i p)
      (referenceTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j p) j
      (smoothSphereValue_referenceTangentRotationJetsFamily_product g L y0 Φ B ε C ρ H a w hData i j p))
  have hProduct : (referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i p)
      (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2:ℝ)) (EuclideanSpace.single j 1)
        (sphereSobolevRotationL (1/2:ℝ) j i u)) =
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j p)
      (sphereSobolevRotationL (1/2:ℝ) j i u) := by
    simpa only [ContinuousLinearMap.comp_apply, referenceTangentBoundaryMultiplierFamily] using hPoint
  have hOrderPoint := congrArg
    (fun T : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      T (sphereSobolevRotationL (1/2:ℝ) j i u))
    (sphereSobolevLinearCoordinateMulL_negative_half_notation_eq hF hO hD (EuclideanSpace.single j 1))
  exact (congrArg
    (referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i p)
    hOrderPoint).trans hProduct

lemma sphereSobolevDualPairing_referenceTangentialHalfRotation_adjoint
    (p : ℝ × (R3 × ℝ)) (u v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) v
      (referenceTangentialHalfRotationFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u) =
    sphereSobolevDualPairing (1/2:ℝ) u
      (referenceTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v) := by
  unfold referenceTangentialHalfRotationFamily referenceTangentialAdjointHalfFamily
  simp only [ContinuousLinearMap.sum_apply,sphereSobolevDualPairing,inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact sphereSobolevDualPairing_nativeHalfCoefficientRotation_adjoint hcalc hF hO hD τ0
    (referenceTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j p) j i u v

lemma sphereSobolevDualPairing_referenceTangentialLower_adjoint
    (p : ℝ × (R3 × ℝ)) (u v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) v
      ((∑ i : Fin 3, (referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i p).comp
        (sphereTangentialDerivativeL hF hO hD i)) u) =
    sphereSobolevDualPairing (1/2:ℝ) u
      (referenceTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v) :=
  (congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevDualPairing (1/2:ℝ) v (T u))
      (referenceTangentialLowerFamily_eq_rotation g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)).trans
    (sphereSobolevDualPairing_referenceTangentialHalfRotation_adjoint g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p u v)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothSphereValue_referenceTangentRotationJetsFamily_product
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentialHalfRotationFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentialLowerFamily_eq_rotation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTangentialHalfRotation_adjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTangentialLower_adjoint
