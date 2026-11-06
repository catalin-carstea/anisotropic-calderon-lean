import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.ActualFiveHalfRadialNativeTaylor
import Calderon.ActualFiveHalfRadialNativeJets
import Calderon.ActualFiveHalfRadialTaylorJets
import Calderon.ActualFiveHalfAdjointMovingInRoom
import Calderon.ActualRadiusScaledMovingAlgebra
import Calderon.ActualConstantModeHorizontalIdentities
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame

private lemma moving_taylor_vector_algebra
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r c ell : ℝ) (hr : r ≠ 0) (hCoeff : r*c=ell) (om bm dm tm j b d t : V) :
    r⁻¹ • (-om+(bm+r • dm+r^2 • tm))+r • j+c • (b+r • d+r^2 • t) =
      r⁻¹ • (-om+bm)+c • b+(dm+ell • d)+r • (tm+j+ell • t) := by
  subst ell
  have hInv : r⁻¹*r=1 := inv_mul_cancel₀ hr
  have hInvSq : r⁻¹*r^2=r := by rw [pow_two,←mul_assoc,hInv,one_mul]
  simp only [smul_add,smul_neg,smul_smul,hInv,hInvSq,one_smul]
  module

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace referenceAdjointFiveHalfRadialFamily
  referenceFiveHalfAdjointRadialSecondRemainder referenceFiveHalfAdjointMovingBoundaryInRoom
  referenceFiveHalfAdjointCoordinateBoundaryFamily referenceNativeMovingAdjointParametricCorrection
  sphereSobolevInclusionL sphereSobolevRadialDriftAdjointL sphereSobolevShiftedDegreeL
  sphereSobolevAngularCoordinateTransposeL sphereSobolevConstantOne

variable (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)

def referenceFiveHalfAdjointMovingRegularRemainderInRoom
    (t : (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)) (i : Fin 3) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (referenceFiveHalfAdjointRadialSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t.1).comp
      (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single i 1)) +
  referenceFiveHalfAdjointJacobiBoundaryInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 t.1 i +
  t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i)) •
    referenceFiveHalfAdjointRadialSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t.1

theorem referenceFiveHalfAdjointMovingBoundaryInRoom_native_decomposition_apply
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (R : R3 → ℝ) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3)
    (hR : DifferentiableAt ℝ R y) (hr : R y ≠ 0)
    (hSegment : ∀ t ∈ uIcc (0:ℝ) (R y), (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (u : SphereSobolev (5/2:ℝ)) :
    referenceFiveHalfAdjointMovingBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R (q,y) i u =
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (5/2:ℝ) i u +
      referenceRadiusHorizontalLogDerivative g L q R y i • sphereSobolevShiftedDegreeL (5/2:ℝ) u +
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (5/2:ℝ)
          ((q,y),fderiv ℝ R y) i u) +
      R y • referenceFiveHalfAdjointMovingRegularRemainderInRoom
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg E ((q,(y,R y)),fderiv ℝ R y) i u := by
  have hTaylor := referenceAdjointFiveHalfRadialFamily_signed_native_taylor
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy (R y) hSegment
  have hCoeff := referenceRadiusHorizontalLogDerivative_mul_radius g L q R y i hR hr
  let M := sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single i 1)
  let om := ∑ j : Fin 3, sphereSobolevRotationL (5/2:ℝ) j i
    (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single j 1) u)
  let J := referenceFiveHalfAdjointJacobiBoundaryInRoom g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 (q,(y,R y)) i
  let Rad := referenceAdjointFiveHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))
  have hMu := congrArg (fun A : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) => A (M u)) hTaylor
  have hU := congrArg (fun A : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) => A u) hTaylor
  simp (config := { instances := true }) only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at hMu hU
  have hLiteral : referenceFiveHalfAdjointMovingBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R (q,y) i u =
      (R y)⁻¹ • (-om+Rad (M u))+R y • J u+
        referenceRadiusHorizontalLogDerivative g L q R y i • Rad u := by
    have h := referenceFiveHalfAdjointMovingBoundaryInRoom_apply
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R (q,y) i u
    simpa only [referenceFiveHalfAdjointCoordinateBoundaryFamily,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,M,om,J,Rad] using h
  have hChange := congrArg₂ (fun x z : SphereSobolev (3/2:ℝ) =>
    (R y)⁻¹ • (-om+x)+R y • J u+referenceRadiusHorizontalLogDerivative g L q R y i • z) hMu hU
  have hAlgebra := moving_taylor_vector_algebra (R y)
    (referenceRadiusHorizontalLogDerivative g L q R y i)
    (fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))) hr hCoeff
    (∑ j : Fin 3, sphereSobolevRotationL (5/2:ℝ) j i
      (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single j 1) u))
    (sphereSobolevShiftedDegreeL (5/2:ℝ)
      (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single i 1) u))
    ((sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
      (sphereSobolevRadialDriftAdjointL hF hO hD (5/2:ℝ) (referenceCenterDrift g L q y))
      (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single i 1) u))
    (referenceFiveHalfAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (q,(y,R y)) (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single i 1) u))
    (referenceFiveHalfAdjointJacobiBoundaryInRoom g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 (q,(y,R y)) i u)
    (sphereSobolevShiftedDegreeL (5/2:ℝ) u)
    ((sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
      (sphereSobolevRadialDriftAdjointL hF hO hD (5/2:ℝ) (referenceCenterDrift g L q y)) u)
    (referenceFiveHalfAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) u)
  have hAll := hLiteral.trans (hChange.trans hAlgebra)
  simpa (config := { instances := true }) only [M,om,J,Rad,sphereSobolevAngularCoordinateTransposeL,
    referenceNativeMovingAdjointParametricCorrection,referenceFiveHalfAdjointMovingRegularRemainderInRoom,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,map_add,map_smul] using hAll

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
