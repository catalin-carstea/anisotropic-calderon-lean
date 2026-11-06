import Calderon.ActualReferenceRotationLowerRadialCovariance
import Calderon.ActualReferenceRotationAdjointHalfRadialDuality
import Calderon.ActualReferenceAdjointHalfRadialDuality
import Calderon.SphereSobolevDualOrthogonalPullback
import Calderon.SphereSobolevCoordinateOrthogonalCovariance
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic SmoothSphereRotation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

lemma referenceRotationAdjointHalfRadialFamily_coordinate_covariance
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (v : SphereSobolev (1/2:ℝ)) :
    referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ) v) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ)
      (referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v) := by
  let e := coordinateRotationIsometry i j θ
  let U := sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
  let V := sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
  let P := referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Pt := referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
  let A := referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let At := referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
  apply sphereSobolev_eq_of_dualPairing_eq (1/2:ℝ)
  intro f
  let u := sphereSobolevOrthogonalPullbackL (1/2:ℝ) e.symm f
  have hback : U u = f := by
    simpa only [LinearIsometryEquiv.symm_symm] using
      sphereSobolevOrthogonalPullbackL_symm_apply (1/2:ℝ) e.symm f
  have hCov : Pt (U u) = V (P u) :=
    referenceRotationLowerRadialEndpointFamily_coordinate_covariance
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j θ p hNormal hStrong hWeak u
  have hRot : sphereSobolevDualPairing (1/2:ℝ) (U v) (Pt (U u)) =
      sphereSobolevDualPairing (1/2:ℝ) (U u) (At (U v)) :=
    sphereSobolevDualPairing_referenceRotationLowerRadial_adjoint
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD i j (θ,p) hWeak (U u) (U v)
  have hBase : sphereSobolevDualPairing (1/2:ℝ) v (P u) =
      sphereSobolevDualPairing (1/2:ℝ) u (A v) :=
    sphereSobolevDualPairing_referenceLowerRadial_adjoint
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD p hWeak u v
  have hPair : sphereSobolevDualPairing (1/2:ℝ) (U u) (At (U v)) =
      sphereSobolevDualPairing (1/2:ℝ) (U u) (V (A v)) :=
    hRot.symm.trans ((congrArg (sphereSobolevDualPairing (1/2:ℝ) (U v)) hCov).trans
      ((sphereSobolevDualPairing_orthogonalPullback (1/2:ℝ) e v (P u)).trans
        (hBase.trans (sphereSobolevDualPairing_orthogonalPullback (1/2:ℝ) e u (A v)).symm)))
  simpa only [hback] using hPair

lemma referenceRotationAdjointThreeHalfRadialFamily_coordinate_covariance
    (hreg : FixedDirichletRegularity) (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (u : SphereSobolev (3/2:ℝ)) :
    referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
      (sphereSobolevOrthogonalPullbackL (3/2:ℝ) (coordinateRotationIsometry i j θ) u) =
    sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ)
      (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u) := by
  let e := coordinateRotationIsometry i j θ
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Uh := sphereSobolevOrthogonalPullbackL (3/2:ℝ) e
  let Ul := sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
  let V := sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
  let Ah := referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Al := referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Ath := referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
  let Atl := referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
  have hRot : J (Ath (Uh u)) = Atl (I (Uh u)) :=
    congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T (Uh u))
      (referenceRotationAdjointRadialEndpointFamily_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j hreg (θ,p) hWeak)
  have hBase : J (Ah u) = Al (I u) :=
    congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
      (referenceAdjointRadialEndpointFamily_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p hWeak)
  have hInput : I (Uh u) = Ul (I u) :=
    sphereSobolevInclusionL_orthogonalPullback_apply (3/2:ℝ) (1/2:ℝ) (by norm_num) e u
  have hOutput : J (Ul (Ah u)) = V (J (Ah u)) :=
    sphereSobolevInclusionL_orthogonalPullback_apply (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) e (Ah u)
  have hCov : Atl (Ul (I u)) = V (Al (I u)) :=
    referenceRotationAdjointHalfRadialFamily_coordinate_covariance
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j θ p hNormal hStrong hWeak (I u)
  have hOne : J (Ath (Uh u)) = Atl (Ul (I u)) :=
    hRot.trans (congrArg Atl hInput)
  have hTwo : J (Ath (Uh u)) = V (Al (I u)) :=
    hOne.trans hCov
  have hThree : J (Ath (Uh u)) = V (J (Ah u)) :=
    hTwo.trans (congrArg V hBase).symm
  have hFour : J (Ath (Uh u)) = J (Ul (Ah u)) :=
    hThree.trans hOutput.symm
  have hInjective : Function.Injective J :=
    sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hFinal : Ath (Uh u) = Ul (Ah u) := hInjective hFour
  simpa only [Ath, Uh, Ul, Ah, e] using hFinal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointHalfRadialFamily_coordinate_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointThreeHalfRadialFamily_coordinate_covariance
