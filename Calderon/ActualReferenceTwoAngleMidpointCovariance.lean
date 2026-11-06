import Calderon.ActualReferenceTwoAngleMidpointCore
import Calderon.ActualReferenceTwoAngleStrongLiftCovariance
import Calderon.SphereSobolevDenseEndpointCovariance

/-! Actual uncompressed midpoint covariance. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
open SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


open NativePolynomialBulkMoments NativeHarmonicHalfCoarseDualPairing
  NativeFullSharpHalfTrace NativeHalfTraceRightInverse

open NativeCoefficientBoundaryMultiplier NativeBoundaryCoefficientFamilies

attribute [local irreducible] referenceTwoAngleSharpMidpointRadialTraceFamily
  sphereSobolevInclusionL sphereSobolevOrthogonalPullbackL

lemma referenceTwoAngleSharpMidpointRadialTraceFamily_first_angle_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp0 : (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (hpθ : (θ,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (f : SphereSobolev 1) :
    referenceTwoAngleSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p))
      (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ) f) =
    sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ)
      (referenceTwoAngleSharpMidpointRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p)) f) := by
  let e := coordinateRotationIsometry i j θ
  let Mθ := referenceTwoAngleSharpMidpointRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p))
  let M0 := referenceTwoAngleSharpMidpointRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p))
  let I := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  have hInner : (referenceRotationStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)).IsInvertible := by
    have hi := hp0.2
    change (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (0,(φ,p))).IsInvertible at hi
    rw [referenceTwoAngleStrongDirichletFamily_zero_outer_angle] at hi
    exact hi
  have hSharp0 := referenceTwoAngleSharpRadialTraceFamily_zero_outer_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l φ p
  have hMθ (u : SphereSobolev (3/2:ℝ)) : Mθ (I u) = J
      (referenceTwoAngleSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p)) u) :=
    congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T u)
      (referenceTwoAngleSharpMidpointRadialTraceFamily_upper_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p)) hpθ)
  have hM0 (u : SphereSobolev (3/2:ℝ)) : M0 (I u) = J
      (referenceRotationSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l (φ,p) u) := by
    have hi := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T u)
      (referenceTwoAngleSharpMidpointRadialTraceFamily_upper_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p)) hp0)
    exact hi.trans (congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => J (T u)) hSharp0)
  apply denseRange_clm_apply_eq I (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))
    (Mθ.comp (sphereSobolevOrthogonalPullbackL 1 e))
    ((sphereSobolevOrthogonalPullbackL 0 e).comp M0)
  intro u
  have hIn := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 1 => T u)
    (sphereSobolevInclusionL_orthogonalPullback (3/2:ℝ) 1 (by norm_num) e)
  have hCov := referenceTwoAngleSharpRadialTraceFamily_outer_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l θ φ p hp0.1.2.2.2.1 hInner hpθ.2 u
  have hOut := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev 0 => T
    (referenceRotationSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l (φ,p) u))
    (sphereSobolevInclusionL_orthogonalPullback (1/2:ℝ) 0 (by norm_num) e)
  exact (congrArg Mθ hIn.symm).trans ((hMθ _).trans
    ((congrArg J hCov).trans (hOut.trans
      (congrArg (sphereSobolevOrthogonalPullbackL 0 e) (hM0 u).symm))))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSharpMidpointRadialTraceFamily_first_angle_covariance
