import Calderon.ActualNativeMovingLocalRemainder
import Calderon.ActualNativeZeroCoordinateCovariantTransport
import Calderon.ActualNativeMovingAdjointCorrectionInclusion

/-! Object5 of actual-native-moving-local-remainder-author-oct16-v001/EXPANSION-v001.md.
Same quotient at two placements, using actual graphs and no desired inverse/gain. -/
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
  referenceHighAdjointCoordinateBoundaryFamily referenceLowerAdjointCoordinateBoundaryFamily

lemma referenceAdjointMovingDifferenceQuotient_high_lower_compatibility
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) =
    (referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let f := referenceRadiusHorizontalLogDerivative g L q R y i
  have hpFields : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp
  unfold referenceRadialEndpointInvertibleLocus at hpFields
  have hp0 := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hp0Fields : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp0
  unfold referenceRadialEndpointInvertibleLocus at hp0Fields
  have hHighZero := referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
  have hLowZero := referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
  have hCoord := referenceAdjointCoordinateBoundaryFamily_high_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,0)) i hp0Fields.2.1
  have hMoving := referenceAdjointMovingBoundaryActionFamily_high_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i hInv hpFields.2.1
  apply ContinuousLinearMap.ext
  intro u
  have hA : Iout (sphereHighHarmonicDerivativeTransposeL hF hO hD i u) =
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (Iin u) := by
    have h1 := congrArg Iout (congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T u) hHighZero)
    have h2 := congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u) hCoord
    have h3 := congrArg
      (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (Iin u)) hLowZero
    exact h1.symm.trans (h2.trans h3)
  have hB : Iout (sphereSobolevShiftedDegreeL (3/2 : ℝ) u) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (Iin u) :=
    congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u)
      sphereSobolevShiftedDegree_high_half_compatibility
  have hCorrection : Iout (Iin (referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i u)) =
      Iout (referenceNativeMovingAdjointParametricCorrection
        hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i (Iin u)) :=
    congrArg Iout (referenceNativeMovingAdjointParametricCorrection_inclusion
      hF hO hD g L (3/2 : ℝ) (1/2 : ℝ) (by norm_num) ((q,y),fderiv ℝ R y) i u)
  have hBase := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b)
    (congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => (R y)⁻¹ • a+f • b) hA hB)
    hCorrection
  have hBaseValue :
      Iout (((R y)⁻¹ • sphereHighHarmonicDerivativeTransposeL hF hO hD i +
        f • sphereSobolevShiftedDegreeL (3/2 : ℝ) +
        Iin.comp (referenceNativeMovingAdjointParametricCorrection
          hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i)) u) =
      (((R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i +
        f • sphereSobolevShiftedDegreeL (1/2 : ℝ) +
        Iout.comp (referenceNativeMovingAdjointParametricCorrection
          hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i)) (Iin u)) := by
    simpa (config := { instances := true }) only
      [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply,map_add,map_smul] using hBase
  have hC := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u) hMoving
  have hValue := congrArg₂ (fun c b : SphereSobolev (-(1/2 : ℝ)) => (R y)⁻¹ • (c-b)) hC hBaseValue
  simpa (config := { instances := true }) only
    [referenceHighAdjointMovingDifferenceQuotient,referenceLowerAdjointMovingDifferenceQuotient,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply,map_smul,map_sub,Iin,Iout,f] using hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMovingDifferenceQuotient_high_lower_compatibility
