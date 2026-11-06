import Calderon.ActualLowerMovingBoundaryAction
import Calderon.SphereSobolevTangentialEndpointCompatibility
import Calderon.ActualReferenceAdjointRadialEndpointFamilies
import Calderon.NativeCoefficientRotationAdjointEndpointCompatibility

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier

/-! The genuine adjoint radial family; no identification with the moving
distributional transpose is assumed. -/

attribute [local irreducible] referenceJacobiBoundaryCoefficientJets
  referenceLowerRadialEndpointFamily referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceHighAdjointCoordinateBoundaryFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  -(∑ j : Fin 3, (sphereSobolevRotationL (3/2 : ℝ) j i).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1))) +
  (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1))

def referenceLowerAdjointCoordinateBoundaryFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  -(∑ j : Fin 3, (sphereSobolevRotationL (1/2 : ℝ) j i).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1))) +
  (referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1))

theorem referenceAdjointCoordinateBoundaryFamily_high_lower_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i) =
    (referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  apply ContinuousLinearMap.ext
  intro f
  have hM (j : Fin 3) :
      Iin (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
        (EuclideanSpace.single j 1) f) =
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single j 1) (Iin f) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD
      (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (EuclideanSpace.single j 1) f
  have hT (j : Fin 3) :
      Iout (sphereSobolevRotationL (3/2 : ℝ) j i
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
          (EuclideanSpace.single j 1) f)) =
      sphereSobolevRotationL (1/2 : ℝ) j i
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single j 1) (Iin f)) := by
    have hR := congrArg
      (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        A (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
          (EuclideanSpace.single j 1) f))
      (sphereSobolevRotationL_threehalf_half_compatibility j i)
    exact hR.trans (congrArg (sphereSobolevRotationL (1/2 : ℝ) j i) (hM j))
  have hR := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      A (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
        (EuclideanSpace.single i 1) f))
    (referenceAdjointRadialEndpointFamily_high_half_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p hWeak)
  have hRad := hR.trans (congrArg
    (referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (hM i))
  simp only [ContinuousLinearMap.comp_apply,referenceHighAdjointCoordinateBoundaryFamily,
    referenceLowerAdjointCoordinateBoundaryFamily,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,map_add,map_neg,map_sum]
  exact congrArg₂ (fun u v => -u + v)
    (Finset.sum_congr rfl (fun j hj => hT j)) hRad

variable (hg : IsAdmissibleMetric g)

def referenceJacobiBoundaryThreeHalfCoefficientJets
    (q : ℝ) (y : R3) (r : ℝ) (i j : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) : SmoothCoefficientJets 3 :=
  compactCoefficient 3
    (coefficientValue 2 (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv))
    (contDiff_coefficientValue 2 _)
    (hasCompactSupport_coefficientValue 2 _)

theorem coefficientValue_referenceJacobiBoundaryThreeHalfCoefficientJets
    (q : ℝ) (y : R3) (r : ℝ) (i j : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    coefficientValue 3
      (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv) =
    coefficientValue 2
      (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv) :=
  coefficientValue_compactCoefficient 3 _ _ _

attribute [local irreducible] referenceJacobiBoundaryThreeHalfCoefficientJets
  referenceHighAdjointCoordinateBoundaryFamily referenceLowerAdjointCoordinateBoundaryFamily

def referenceHighAdjointJacobiBoundaryCorrection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ j : Fin 3, (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j).comp
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv))

def referenceLowerAdjointJacobiBoundaryCorrection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ∑ j : Fin 3, (referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j).comp
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv))

theorem referenceAdjointJacobiBoundaryCorrection_high_lower_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,r))).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv) =
    (referenceLowerAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  apply ContinuousLinearMap.ext
  intro f
  have hTerm (j : Fin 3) :
      Iout (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv) f)) =
      referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv) (Iin f)) := by
    have hQ := congrArg
      (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        A (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv) f))
      (referenceAdjointCoordinateBoundaryFamily_high_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,r)) j hWeak)
    have hM := congrArg
      (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A f)
      (NativeOrderOneCoefficientMultiplier.nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv)
        (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)
        (coefficientValue_referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv))
    exact hQ.trans (congrArg
      (referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j) hM)
  simp only [ContinuousLinearMap.comp_apply,referenceHighAdjointJacobiBoundaryCorrection,
    referenceLowerAdjointJacobiBoundaryCorrection,ContinuousLinearMap.sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun j hj => hTerm j)

def referenceHighAdjointMovingBoundaryAction
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (R y)⁻¹ • referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i +
  (R y) • referenceHighAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y) i hInv +
  referenceRadiusHorizontalLogDerivative g L q R y i •
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))

def referenceLowerAdjointMovingBoundaryAction
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  (R y)⁻¹ • referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i +
  (R y) • referenceLowerAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y) i hInv +
  referenceRadiusHorizontalLogDerivative g L q R y i •
    referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))

attribute [local irreducible] referenceHighAdjointJacobiBoundaryCorrection
  referenceLowerAdjointJacobiBoundaryCorrection referenceHighAdjointMovingBoundaryAction
  referenceLowerAdjointMovingBoundaryAction

theorem referenceAdjointMovingBoundaryAction_high_lower_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv) =
    (referenceLowerAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  have hQ := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
    (referenceAdjointCoordinateBoundaryFamily_high_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,R y)) i hWeak)
  have hJ := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
    (referenceAdjointJacobiBoundaryCorrection_high_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q y (R y) i hInv hWeak)
  have hR := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
    (referenceAdjointRadialEndpointFamily_high_half_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,R y)) hWeak)
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a + b)
    (congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a + b)
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => (R y)⁻¹ • z) hQ)
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => R y • z) hJ))
    (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      referenceRadiusHorizontalLogDerivative g L q R y i • z) hR)
  simpa only [referenceHighAdjointMovingBoundaryAction,referenceLowerAdjointMovingBoundaryAction,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    map_add,map_smul] using hCombined

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointCoordinateBoundaryFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointCoordinateBoundaryFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointCoordinateBoundaryFamily_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceJacobiBoundaryThreeHalfCoefficientJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceJacobiBoundaryThreeHalfCoefficientJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointJacobiBoundaryCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointJacobiBoundaryCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointJacobiBoundaryCorrection_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingBoundaryAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointMovingBoundaryAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMovingBoundaryAction_high_lower_compatibility
