import Calderon.ActualJacobiSphereSmoothCoefficient
import Calderon.ActualReferenceLowerBoundaryTranspose
import Calderon.ActualReferenceRadialInvertibleEndpointCompatibility
import Calderon.NativeH2TangentialTrace
import Calderon.NativeNegativeHalfCoefficientCoordinateProduct
import Calderon.ActualNativeMovingRadiusTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeFullSharpHalfTrace
  NativeHarmonicLiftCompletion NativeCoefficientBoundaryMultiplier
  NativeNegativeHalfCoefficientCoordinateProduct

/-! The actual boundary action at the H1/2 to H-1/2 endpoint. -/

attribute [local irreducible] referenceHarmonicLiftFamily harmonicLiftCompletion
  referenceJacobiBoundaryCoefficientJets referenceJacobiSphereCoefficient
  referenceLowerRadialEndpointFamily strongCoordinateTraceL outwardRadialTraceL
  sphereTangentialDerivativeL nativeNegativeHalfCoefficientMulL
  referenceNativeCoordinateTraceOperatorFamily referenceNativeRadialTraceOperatorFamily
  referenceNativeJacobiTraceCorrection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceLowerCoordinateBoundaryFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  sphereTangentialDerivativeL hF hO hD i +
    (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
      (EuclideanSpace.single i 1)).comp
        (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)

attribute [local irreducible] referenceLowerCoordinateBoundaryFamily

theorem referenceLowerCoordinateBoundaryFamily_eq_coarse_coordinate
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) =
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0
          p.1 i p.2 (harmonicLiftCompletion hF f))) := by
  let U : BallSobolev 2 := referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 (harmonicLiftCompletion hF f)
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let M := sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
    (EuclideanSpace.single i 1)
  have hTrace : nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) = I f :=
    nativeHalfTraceL_firstOrder_referenceHarmonicLiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2 hStrong f
  have hT : sphereTangentialDerivativeL hF hO hD i (I f) =
      J (Z (strongCoordinateTraceL hcalc τ0 i U -
        sphereCoordinateMulL i (outwardRadialTraceL hcalc τ0 U))) := by
    have ht := sphereTangentialDerivativeL_nativeHalfTrace_H2 hcalc hF hO hD τ0 U i
    rw [hTrace] at ht
    have hJ : sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num) = J := by
      dsimp only [J]
      unfold sphereSobolevInclusionL
      simp only [neg_div]
    rw [hJ] at ht
    exact ht
  have hRad : referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p (I f) =
      J (Z (outwardRadialTraceL hcalc τ0 U)) :=
    referenceLowerRadialEndpointFamily_inclusion_eq_coarse_radial_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hNormal hStrong hWeak f
  have hM : M (J (Z (outwardRadialTraceL hcalc τ0 U))) =
      J (Z (sphereCoordinateMulL i (outwardRadialTraceL hcalc τ0 U))) := by
    have hi := sphereSobolevInclusionL_linearCoordinateMul hF hO hD 0 (-(1/2 : ℝ))
      (by norm_num) (EuclideanSpace.single i 1) (Z (outwardRadialTraceL hcalc τ0 U))
    have hz := sphereSobolevLinearCoordinateMulL_zeroEquiv hF hO hD
      (EuclideanSpace.single i 1) (outwardRadialTraceL hcalc τ0 U)
    have hs := congrArg (fun A : SphereL2 →L[ℝ] SphereL2 =>
      Z (A (outwardRadialTraceL hcalc τ0 U))) (sphereLinearCoordinateMulL_single i)
    exact hi.symm.trans (congrArg J (hz.trans hs))
  simp only [referenceLowerCoordinateBoundaryFamily, add_apply,
    ContinuousLinearMap.comp_apply, referenceNativeCoordinateTraceOperatorFamily]
  change sphereTangentialDerivativeL hF hO hD i (I f) +
    M (referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p (I f)) =
      J (Z (strongCoordinateTraceL hcalc τ0 i U))
  have hSum := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a + b)
    hT ((congrArg M hRad).trans hM)
  exact hSum.trans (by simp only [map_sub, sub_add_cancel])

variable (hg : IsAdmissibleMetric g)

def referenceLowerJacobiBoundaryCorrection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ∑ j : Fin 3, (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)).comp
      (referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 (q,(y,r)) j)

def referenceLowerCenterBoundaryAction
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  r⁻¹ • referenceLowerCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) i +
  r • referenceLowerJacobiBoundaryCorrection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv

def referenceLowerMovingBoundaryAction
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  referenceLowerCenterBoundaryAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y) i hInv +
  referenceRadiusHorizontalLogDerivative g L q R y i •
    referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))

attribute [local irreducible] referenceLowerJacobiBoundaryCorrection
  referenceLowerCenterBoundaryAction referenceLowerMovingBoundaryAction

theorem referenceLowerJacobiBoundaryCorrection_eq_coarse_jacobi
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,r))).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceLowerJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg
      hcalc hF hO hD τ0 q y r i hInv
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) =
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (referenceNativeJacobiTraceCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc τ0
          q y r i hInv (harmonicLiftCompletion hF f))) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let E := harmonicLiftCompletion hF f
  have hTerm (j : Fin 3) :
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)
        (referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 (q,(y,r)) j (I f)) =
      J (Z (sphereContinuousScalarMulL
        (referenceJacobiSphereCoefficient g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)
        (referenceNativeCoordinateTraceOperatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc τ0 q j (y,r) E))) := by
    rw [referenceLowerCoordinateBoundaryFamily_eq_coarse_coordinate
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j
      hNormal hStrong hWeak f]
    have hm := nativeNegativeHalfCoefficientMulL_zero_inclusion hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)
      (Z (referenceNativeCoordinateTraceOperatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc τ0 q j (y,r) E))
    rw [smoothSphereValue_referenceJacobiBoundaryCoefficientJets] at hm
    simpa only [J,Z,E,LinearIsometryEquiv.symm_apply_apply] using hm
  simp only [referenceLowerJacobiBoundaryCorrection,referenceNativeJacobiTraceCorrection,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [I, J, Z, E] using hTerm j

theorem referenceLowerMovingBoundaryAction_eq_coarse_moving
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceLowerMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg
      hcalc hF hO hD τ0 q R y i hInv
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) =
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (referenceNativeMovingRadiusTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0
          q R y i hInv (harmonicLiftCompletion hF f))) := by
  have hQ := referenceLowerCoordinateBoundaryFamily_eq_coarse_coordinate
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i hNormal hStrong hWeak f
  have hJ := referenceLowerJacobiBoundaryCorrection_eq_coarse_jacobi
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y) i hInv
      hNormal hStrong hWeak f
  have hRad := referenceLowerRadialEndpointFamily_inclusion_eq_coarse_radial_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))
      hNormal hStrong hWeak f
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a + b)
    (congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a + b)
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => (R y)⁻¹ • z) hQ)
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => R y • z) hJ))
    (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      referenceRadiusHorizontalLogDerivative g L q R y i • z) hRad)
  simpa only [referenceLowerMovingBoundaryAction, referenceLowerCenterBoundaryAction,
    referenceNativeMovingRadiusTraceOperator, referenceNativeCenterTraceOperator,
    add_apply, smul_apply, referenceNativeRadialTraceOperatorFamily,
    ContinuousLinearMap.comp_apply, map_add, map_smul] using hCombined

def referenceLowerMovingBoundaryTranspose
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  sphereLowerDistributionalTranspose (referenceLowerMovingBoundaryAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv)

theorem sphereSobolevDualPairing_referenceLowerMovingBoundaryTranspose
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (referenceLowerMovingBoundaryAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv u) =
    sphereSobolevDualPairing (1/2 : ℝ) u
      (referenceLowerMovingBoundaryTranspose
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv v) :=
  sphereSobolevDualPairing_lower_distributionalTranspose _ u v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerCoordinateBoundaryFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerCoordinateBoundaryFamily_eq_coarse_coordinate
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerJacobiBoundaryCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerCenterBoundaryAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerMovingBoundaryAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerJacobiBoundaryCorrection_eq_coarse_jacobi
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerMovingBoundaryAction_eq_coarse_moving
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerMovingBoundaryTranspose
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceLowerMovingBoundaryTranspose
