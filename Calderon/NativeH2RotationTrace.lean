import Calderon.NativeH2BoundaryRotationGreen
import Calderon.SphereSobolevOrderOneRotation

set_option autoImplicit false
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  SmoothSphereRotation SmoothSphereRotationProjection SmoothAngularCasimir
  NativeFullSharpHalfTrace SpectralCoreRegularity AngularPolynomial GreenRadialTrace

theorem sphereHarmonicCoordinate_nativeH2_rotation
    (hcalc : FixedSobolevCalculus) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (U : BallSobolev 2) (k : ℕ) (i j : Fin 3) :
    sphereHarmonicCoordinate hO hD k
      (sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i U) -
        sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j U)) =
      harmonicSphereRotation k j i
        (sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U))) := by
  apply ext_inner_right ℝ
  intro v
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨p,rfl⟩
  rw [sphereHarmonicCoordinate_inner hO hD k _ (harmonicPolynomialSphereMap k p),
    inner_harmonicSphereRotation_skew,
    sphereHarmonicCoordinate_inner hO hD k _
      (harmonicSphereRotation k j i (harmonicPolynomialSphereMap k p)),
    harmonicSphereRotation_apply_image]
  change ⟪sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i U) -
      sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j U),polynomialSphereL2 p⟫_ℝ =
    -⟪τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U),
      polynomialSphereL2 (polynomialRotation j i p)⟫_ℝ
  have h := nativeH2_boundary_rotation_inner_smooth hcalc τ0 U
    (⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩ : SmoothData) i j
  rw [τ0.valueTrace_smooth] at h
  change ⟪sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i U) -
      sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j U),
      smoothSphereLift (polynomialEvaluation p) (contDiff_polynomialEvaluation p)⟫_ℝ =
    -⟪τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U),
      smoothSphereLift (sphereRotationDerivative j i (polynomialEvaluation p))
        (contDiff_sphereRotationDerivative j i _ (contDiff_polynomialEvaluation p))⟫_ℝ at h
  rw [smoothSphereLift_polynomialEvaluation,smoothSphereLift_rotation_polynomial] at h
  exact h

theorem sphereSobolevRotationL_nativeHalfTrace_H2
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 2) (i j : Fin 3) :
    sphereSobolevRotationL (1/2 : ℝ) j i
      (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)) =
    sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i U) -
          sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j U))) := by
  apply sphereSobolev_ext (-1/2 : ℝ)
  intro k
  have hs : (1/2 : ℝ)-1 = -1/2 := by norm_num
  have hrot : sphereSobolevCoefficientL (-1/2 : ℝ) k
      (sphereSobolevRotationL (1/2 : ℝ) j i
        (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U))) =
      harmonicSphereRotation k j i
        (sphereSobolevCoefficientL (1/2 : ℝ) k
          (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U))) := by
    simpa only [sphereSobolevCoefficientL,hs] using
      sphereSobolevCoefficientL_rotation (1/2 : ℝ) j i k
        (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U))
  rw [hrot,sphereSobolevCoefficientL_nativeHalfTraceL,
    sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv,
    sphereHarmonicCoordinate_nativeH2_rotation]

end OAI.AnisotropicCalderon.SphereHarmonic
