import Calderon.ActualLowerMovingBoundaryAction
import Calderon.SphereSobolevTangentialEndpointCompatibility
import Calderon.ActualReferenceSharpUpperTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeCoefficientBoundaryMultiplier

/-! Upfront: day-oct13/actual-boundary-moving-operator-oct15-v001/
EXPANSION-high-boundary-action.md. SAME actual coefficients and Dirichlet lift.
Only the literal high/lower native endpoints and exact coarse graph are claimed. -/

attribute [local irreducible] referenceHarmonicLiftFamily harmonicLiftCompletion
  referenceJacobiBoundaryCoefficientJets referenceJacobiSphereCoefficient
  referenceLowerRadialEndpointFamily referenceSharpRadialTraceFamily
  sphereThreeHalfTangentialDerivativeL sphereTangentialDerivativeL
  sphereSobolevLinearCoordinateMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL referenceLowerCoordinateBoundaryFamily
  referenceLowerJacobiBoundaryCorrection referenceNativeMovingRadiusTraceOperator

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceHighCoordinateBoundaryFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  sphereThreeHalfTangentialDerivativeL hF hO hD i +
    (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
      (EuclideanSpace.single i 1)).comp
        (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)

attribute [local irreducible] referenceHighCoordinateBoundaryFamily

theorem referenceCoordinateBoundaryFamily_high_lower_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i) =
    (referenceLowerCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Dh := referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Dl := referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  apply ContinuousLinearMap.ext
  intro f
  have hT : Iout (sphereThreeHalfTangentialDerivativeL hF hO hD i f) =
      sphereTangentialDerivativeL hF hO hD i (Iin f) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
      (sphereTangentialDerivativeL_threehalf_half_compatibility hF hO hD i)
  have hRad : Iout (Dh f) = Dl (Iin f) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
      (referenceSharpRadialTraceFamily_lower_compatibility_of_isInvertible
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hNormal hStrong hWeak)
  have hM := sphereSobolevInclusionL_linearCoordinateMul hF hO hD
    (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (EuclideanSpace.single i 1) (Dh f)
  have hCoordinate := hM.trans (congrArg
    (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
      (EuclideanSpace.single i 1)) hRad)
  have hCombined := congrArg₂
    (fun a b : SphereSobolev (-(1/2 : ℝ)) => a + b) hT hCoordinate
  simpa only [referenceHighCoordinateBoundaryFamily,referenceLowerCoordinateBoundaryFamily,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,map_add,Iin,Iout,Dh,Dl]
    using hCombined

variable (hg : IsAdmissibleMetric g)

def referenceHighJacobiBoundaryCorrection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ j : Fin 3, (nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)).comp
      (referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 (q,(y,r)) j)

def referenceHighCenterBoundaryAction
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  r⁻¹ • referenceHighCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) i +
  r • referenceHighJacobiBoundaryCorrection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv

def referenceHighMovingBoundaryAction
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  referenceHighCenterBoundaryAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y) i hInv +
  referenceRadiusHorizontalLogDerivative g L q R y i •
    referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))

attribute [local irreducible] referenceHighJacobiBoundaryCorrection
  referenceHighCenterBoundaryAction referenceHighMovingBoundaryAction
  referenceLowerCenterBoundaryAction referenceLowerMovingBoundaryAction

theorem referenceJacobiBoundaryCorrection_high_lower_compatibility
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
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,r))).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighJacobiBoundaryCorrection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv) =
    (referenceLowerJacobiBoundaryCorrection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  apply ContinuousLinearMap.ext
  intro f
  have hTerm (j : Fin 3) :
      Iout (nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)
        (referenceHighCoordinateBoundaryFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j f)) =
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)
        (referenceLowerCoordinateBoundaryFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j (Iin f)) := by
    have hM := congrArg
      (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        A (referenceHighCoordinateBoundaryFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j f))
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv))
    have hQ := congrArg
      (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
      (referenceCoordinateBoundaryFamily_high_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j hNormal hStrong hWeak)
    exact hM.trans (congrArg
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)) hQ)
  simp only [ContinuousLinearMap.comp_apply,referenceHighJacobiBoundaryCorrection,
    referenceLowerJacobiBoundaryCorrection,ContinuousLinearMap.sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun j hj => hTerm j)

theorem referenceMovingBoundaryAction_high_lower_compatibility
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
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighMovingBoundaryAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv) =
    (referenceLowerMovingBoundaryAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  have hQ := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
    (referenceCoordinateBoundaryFamily_high_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i hNormal hStrong hWeak)
  have hJ := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
    (referenceJacobiBoundaryCorrection_high_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y) i hInv hNormal hStrong hWeak)
  have hR := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
    (referenceSharpRadialTraceFamily_lower_compatibility_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) hNormal hStrong hWeak)
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a + b)
    (congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a + b)
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => (R y)⁻¹ • z) hQ)
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => R y • z) hJ))
    (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      referenceRadiusHorizontalLogDerivative g L q R y i • z) hR)
  simpa only [referenceHighMovingBoundaryAction,referenceHighCenterBoundaryAction,
    referenceLowerMovingBoundaryAction,referenceLowerCenterBoundaryAction,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,map_add,map_smul] using hCombined

theorem referenceHighMovingBoundaryAction_eq_coarse_moving
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
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg
        hcalc hF hO hD τ0 q R y i hInv f) =
    sphereSobolevZeroEquiv hO hD
      (referenceNativeMovingRadiusTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0
        q R y i hInv (harmonicLiftCompletion hF f)) := by
  let Ch := referenceHighMovingBoundaryAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv
  apply sphereSobolevInclusionL_injective 0 (-(1/2 : ℝ)) (by norm_num)
  have hTrans := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (Ch f))
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  have hCompat := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
    (referenceMovingBoundaryAction_high_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv hNormal hStrong hWeak)
  exact hTrans.trans (hCompat.trans (referenceLowerMovingBoundaryAction_eq_coarse_moving
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv
      hNormal hStrong hWeak f))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighCoordinateBoundaryFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceCoordinateBoundaryFamily_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighJacobiBoundaryCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighCenterBoundaryAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighMovingBoundaryAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceJacobiBoundaryCorrection_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceMovingBoundaryAction_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighMovingBoundaryAction_eq_coarse_moving
