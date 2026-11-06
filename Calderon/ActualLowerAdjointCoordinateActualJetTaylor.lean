import Calderon.ActualReferenceAdjointHalfNativeTaylor
import Calderon.ActualReferenceLowerAdjointMovingFirstJet

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceAdjointHalfRadialFamily
  referenceLowerAdjointCoordinateBoundaryFamily referenceRadialEndpointInvertibleLocus
  secondTaylorRemainder sphereSobolevShiftedDegreeL sphereSobolevAngularCoordinateTransposeL
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

lemma referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3) :
    referenceLowerAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i =
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i := by
  have hZero := referenceAdjointHalfRadialFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hChange := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      -(∑ j : Fin 3, (sphereSobolevRotationL (1/2 : ℝ) j i).comp
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single j 1))) +
      A.comp (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1))) hZero
  simpa only [referenceLowerAdjointCoordinateBoundaryFamily,
    sphereSobolevAngularCoordinateTransposeL] using hChange

lemma referenceLowerAdjointCoordinateBoundaryFamily_signed_actual_jet_taylor
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ) (i : Fin 3)
    (hSegment : ∀ t ∈ uIcc (0 : ℝ) r, (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceLowerAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) i =
      referenceLowerAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i +
      r • (deriv (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0).comp
          (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
            (EuclideanSpace.single i 1)) +
      r^2 • (secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r).comp
          (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
            (EuclideanSpace.single i 1)) := by
  let A : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun t =>
    referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  have hNative := referenceAdjointHalfRadialFamily_signed_native_taylor
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy r hSegment
  have hZero : A 0 = sphereSobolevShiftedDegreeL (1/2 : ℝ) :=
    referenceAdjointHalfRadialFamily_zero_eq_shiftedDegree
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hFirst : deriv A 0 =
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ)
          (referenceCenterDrift g L q y)) :=
    deriv_referenceAdjointHalfRadialFamily_zero_eq_nativeFirstCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hChange := congrArg₂
    (fun Z D : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      Z + r • D + r^2 • secondTaylorRemainder A r) hZero hFirst
  have hTaylor : A r = A 0 + r • deriv A 0 + r^2 • secondTaylorRemainder A r :=
    hNative.trans hChange.symm
  apply ContinuousLinearMap.ext
  intro u
  have hPoint := congrArg (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) => F
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single i 1) u)) hTaylor
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at hPoint
  let P : SphereSobolev (-(1/2 : ℝ)) :=
    -(∑ j : Fin 3, (sphereSobolevRotationL (1/2 : ℝ) j i).comp
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single j 1))) u
  have hShift := congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => P + v) hPoint
  simpa only [referenceLowerAdjointCoordinateBoundaryFamily,A,P,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,add_assoc] using hShift

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointCoordinateBoundaryFamily_signed_actual_jet_taylor
