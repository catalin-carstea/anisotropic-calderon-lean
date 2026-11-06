import Calderon.NativeSmoothSphereRotationAngleDerivative
import Calderon.OrthogonalHarmonicPolynomialPullback
import Calderon.SmoothSphereRotationProjection

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation SmoothAngularCasimir SmoothSphereRotationProjection
  SpectralCoreRegularity GreenRadialTrace

/-! Upfront expansion: EXPANSION-finite-harmonic-angle-derivative-v001.json.
The genuine polynomial image is used; no Fischer injectivity or assumed block covariance. -/

lemma harmonicSphereOrthogonalPullback_eq_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (e : R3 ≃ₗᵢ[ℝ] R3) (k : ℕ) (u : harmonicSphereSubspace k) :
    harmonicSphereOrthogonalPullback e k u =
      sphereHarmonicCoordinate hO hD k (sphereL2OrthogonalPullback e (u : SphereL2)) :=
  (sphereHarmonicCoordinate_subtype hO hD k (harmonicSphereOrthogonalPullback e k u)).symm

lemma contDiff_harmonicSphereOrthogonalPullback_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    ContDiff ℝ ∞ (fun t => harmonicSphereOrthogonalPullback (coordinateRotationIsometry i j t) k u) := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  simp_rw [harmonicSphereOrthogonalPullback_eq_coordinate hO hD]
  change ContDiff ℝ ∞ (fun t => sphereHarmonicCoordinate hO hD k
    (sphereL2OrthogonalPullback (coordinateRotationIsometry i j t) (polynomialSphereL2 p)))
  rw [← smoothSphereLift_polynomialEvaluation p]
  apply (sphereHarmonicCoordinate hO hD k).contDiff.comp
  exact contDiff_sphereL2OrthogonalPullback_coordinate_smooth i j
    (polynomialEvaluation p) (contDiff_polynomialEvaluation p)

lemma hasDerivAt_harmonicSphereOrthogonalPullback_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) (t : ℝ) :
    HasDerivAt (fun θ => harmonicSphereOrthogonalPullback (coordinateRotationIsometry i j θ) k u)
      (harmonicSphereOrthogonalPullback (coordinateRotationIsometry i j t) k
        (harmonicSphereRotation k i j u)) t := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  have hd := hasDerivAt_sphereL2OrthogonalPullback_coordinate_smooth i j
    (polynomialEvaluation p) (contDiff_polynomialEvaluation p) t
  rw [smoothSphereLift_polynomialEvaluation,smoothSphereLift_rotation_polynomial] at hd
  have hp := (sphereHarmonicCoordinate hO hD k).hasFDerivAt.comp_hasDerivAt t hd
  convert hp using 1
  · funext θ
    exact harmonicSphereOrthogonalPullback_eq_coordinate hO hD
      (coordinateRotationIsometry i j θ) k (harmonicPolynomialSphereMap k p)
  · rw [harmonicSphereRotation_apply_image]
    exact harmonicSphereOrthogonalPullback_eq_coordinate hO hD
      (coordinateRotationIsometry i j t) k (rotatedHarmonicSphereMap k i j p)

lemma harmonicSphereOrthogonalPullback_coordinate_zero (i j : Fin 3) (k : ℕ)
    (u : harmonicSphereSubspace k) :
    harmonicSphereOrthogonalPullback (coordinateRotationIsometry i j 0) k u = u := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  apply Subtype.ext
  change sphereL2OrthogonalPullback (coordinateRotationIsometry i j 0) (polynomialSphereL2 p) =
    polynomialSphereL2 p
  rw [← smoothSphereLift_polynomialEvaluation p]
  exact sphereL2OrthogonalPullback_coordinate_zero_smooth i j
    (polynomialEvaluation p) (contDiff_polynomialEvaluation p)

lemma hasDerivAt_harmonicSphereOrthogonalPullback_coordinate_zero
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    HasDerivAt (fun θ => harmonicSphereOrthogonalPullback (coordinateRotationIsometry i j θ) k u)
      (harmonicSphereRotation k i j u) 0 := by
  have h := hasDerivAt_harmonicSphereOrthogonalPullback_coordinate hO hD i j k u 0
  rw [harmonicSphereOrthogonalPullback_coordinate_zero] at h
  exact h

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.harmonicSphereOrthogonalPullback_eq_coordinate
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.contDiff_harmonicSphereOrthogonalPullback_coordinate
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_harmonicSphereOrthogonalPullback_coordinate
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.harmonicSphereOrthogonalPullback_coordinate_zero
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_harmonicSphereOrthogonalPullback_coordinate_zero
