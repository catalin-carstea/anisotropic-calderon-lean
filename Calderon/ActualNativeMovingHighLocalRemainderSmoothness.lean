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

lemma contDiffAt_referenceHighAdjointMovingDifferenceQuotient
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun x : R3 => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i) y := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  letI : IsBoundedSMul ℝ
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    IsBoundedSMul.of_norm_smul_le (fun c T => ContinuousLinearMap.opNorm_smul_le c T)
  have hBase : ContDiffAt ℝ ∞ (fun x : R3 => (q,x)) y :=
    contDiffAt_const.prodMk contDiffAt_id
  have hC3 : ContDiffAt ℝ ∞ (fun x : R3 =>
      referenceHighAdjointMovingBoundaryActionFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,x) i) y :=
    (contDiffAt_referenceHighAdjointMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg R (q,y) i hR hr hInv hp).comp y hBase
  have hScalar : ContDiffAt ℝ ∞ (fun x : R3 =>
      referenceRadiusHorizontalLogDerivative g L q R x i) y :=
    (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i hR hr).comp y hBase
  have hInvR : ContDiffAt ℝ ∞ (fun x : R3 => (R x)⁻¹) y := hR.inv hr
  have hDerivative : ContDiffAt ℝ ∞ (fderiv ℝ R) y := hR.fderiv_right (by simp)
  have hParam : ContDiffAt ℝ ∞ (fun x : R3 => ((q,x),fderiv ℝ R x)) y :=
    hBase.prodMk hDerivative
  have hF3 : ContDiffAt ℝ ∞ (fun x : R3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i) y :=
    (contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L (3/2 : ℝ) i).contDiffAt.comp y hParam
  have hA3 : ContDiffAt ℝ ∞ (fun _ : R3 =>
      (sphereHighHarmonicDerivativeTransposeL hF hO hD i :
        SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))) y := contDiffAt_const
  have hB3 : ContDiffAt ℝ ∞ (fun _ : R3 =>
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) :
        SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))) y := contDiffAt_const
  have hBase3 : ContDiffAt ℝ ∞ (fun x : R3 =>
      (R x)⁻¹ • sphereHighHarmonicDerivativeTransposeL hF hO hD i +
      referenceRadiusHorizontalLogDerivative g L q R x i • sphereSobolevShiftedDegreeL (3/2 : ℝ) +
      Iin.comp (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
        ((q,x),fderiv ℝ R x) i)) y :=
    ((hInvR.smul hA3).add (hScalar.smul hB3)).add
      (contDiffAt_const.clm_comp hF3)
  simpa (config := { instances := true }) only
    [referenceHighAdjointMovingDifferenceQuotient,Iin,Pi.smul_def']
    using hInvR.smul (hC3.sub hBase3)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighAdjointMovingDifferenceQuotient
