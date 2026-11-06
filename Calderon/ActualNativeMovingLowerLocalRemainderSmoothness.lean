import Calderon.ActualNativeMovingLocalRemainder
import Calderon.ActualAdjointMovingBoundaryFamilies

/-! Before-source: actual-local-remainder-endpoint-smoothness-author-oct16-v001/EXPANSION-v001.md.
One actual endpoint of the unchanged paired local quotient claim. -/
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
  referenceLowerAdjointMovingDifferenceQuotient referenceRadialEndpointInvertibleLocus

lemma contDiffAt_referenceLowerAdjointMovingDifferenceQuotient
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun x : R3 => referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i) y := by
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  letI : IsBoundedSMul ℝ
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    IsBoundedSMul.of_norm_smul_le (fun c T => ContinuousLinearMap.opNorm_smul_le c T)
  have hpFields : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp
  unfold referenceRadialEndpointInvertibleLocus at hpFields
  have hBase : ContDiffAt ℝ ∞ (fun x : R3 => (q,x)) y :=
    contDiffAt_const.prodMk contDiffAt_id
  have hC1 : ContDiffAt ℝ ∞ (fun x : R3 =>
      referenceLowerAdjointMovingBoundaryActionFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,x) i) y :=
    (contDiffAt_referenceLowerAdjointMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i hR hr hInv
        hpFields.2.2 hpFields.2.1).comp y hBase
  have hScalar : ContDiffAt ℝ ∞ (fun x : R3 =>
      referenceRadiusHorizontalLogDerivative g L q R x i) y :=
    (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i hR hr).comp y hBase
  have hInvR : ContDiffAt ℝ ∞ (fun x : R3 => (R x)⁻¹) y := hR.inv hr
  have hDerivative : ContDiffAt ℝ ∞ (fderiv ℝ R) y := hR.fderiv_right (by simp)
  have hParam : ContDiffAt ℝ ∞ (fun x : R3 => ((q,x),fderiv ℝ R x)) y :=
    hBase.prodMk hDerivative
  have hF1 : ContDiffAt ℝ ∞ (fun x : R3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,x),fderiv ℝ R x) i) y :=
    (contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L (1/2 : ℝ) i).contDiffAt.comp y hParam
  have hA1 : ContDiffAt ℝ ∞ (fun _ : R3 =>
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i :
        SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))) y := contDiffAt_const
  have hB1 : ContDiffAt ℝ ∞ (fun _ : R3 =>
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) :
        SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))) y := contDiffAt_const
  have hBase1 : ContDiffAt ℝ ∞ (fun x : R3 =>
      (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i +
      referenceRadiusHorizontalLogDerivative g L q R x i • sphereSobolevShiftedDegreeL (1/2 : ℝ) +
      Iout.comp (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
        ((q,x),fderiv ℝ R x) i)) y :=
    ((hInvR.smul hA1).add (hScalar.smul hB1)).add
      (contDiffAt_const.clm_comp hF1)
  simpa (config := { instances := true }) only
    [referenceLowerAdjointMovingDifferenceQuotient,Iout,Pi.smul_def']
    using hInvR.smul (hC1.sub hBase1)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceLowerAdjointMovingDifferenceQuotient
