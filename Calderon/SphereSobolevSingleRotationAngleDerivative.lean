import Calderon.HarmonicSphereRotationAngleDerivative
import Calderon.SphereSobolevOrthogonalPullback
import Calderon.SphereSobolevOrderOneRotation

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation SmoothSphereRotationProjection

/-! Upfront expansion: EXPANSION-finite-harmonic-angle-derivative-v001.json.
Same-order angle smoothness is asserted only for a fixed harmonic single. -/

lemma contDiff_sphereSobolevOrthogonalPullback_coordinate_single
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ)
    (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    ContDiff ℝ ∞ (fun θ => sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
      (sphereSobolevSingleL s k u)) := by
  simp_rw [sphereSobolevOrthogonalPullbackL_single]
  apply (sphereSobolevSingleL s k).contDiff.comp
  exact contDiff_harmonicSphereOrthogonalPullback_coordinate hO hD i j k u

lemma hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_single
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ)
    (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) (t : ℝ) :
    HasDerivAt (fun θ => sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
      (sphereSobolevSingleL s k u))
      (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j t)
        (sphereSobolevSingleL s k (harmonicSphereRotation k i j u))) t := by
  simp_rw [sphereSobolevOrthogonalPullbackL_single]
  exact (sphereSobolevSingleL s k).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_harmonicSphereOrthogonalPullback_coordinate hO hD i j k u t)

lemma hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_single_zero
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ)
    (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    HasDerivAt (fun θ => sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
      (sphereSobolevSingleL s k u))
      (sphereSobolevSingleL s k (harmonicSphereRotation k i j u)) 0 := by
  simp_rw [sphereSobolevOrthogonalPullbackL_single]
  exact (sphereSobolevSingleL s k).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_harmonicSphereOrthogonalPullback_coordinate_zero hO hD i j k u)

lemma sphereSobolevRotationL_single (s : ℝ) (i j : Fin 3) (k : ℕ)
    (u : harmonicSphereSubspace k) :
    sphereSobolevRotationL s i j (sphereSobolevSingleL s k u) =
      sphereSobolevSingleL (s-1) k (harmonicSphereRotation k i j u) := by
  apply sphereSobolev_ext (s-1)
  intro l
  rw [sphereSobolevCoefficientL_rotation]
  by_cases hl : l = k
  · subst l
    rw [sphereSobolevCoefficientL_single_self,sphereSobolevCoefficientL_single_self]
  · rw [sphereSobolevCoefficientL_single_ne s k l hl,
      sphereSobolevCoefficientL_single_ne (s-1) k l hl]
    exact (harmonicSphereRotation l i j).map_zero

lemma hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_single_lower_zero
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ)
    (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    HasDerivAt (fun θ => sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
        (sphereSobolevSingleL s k u)))
      (sphereSobolevRotationL s i j (sphereSobolevSingleL s k u)) 0 := by
  have hd := (sphereSobolevInclusionL s (s-1) (by linarith)).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_single_zero hO hD s i j k u)
  have he : sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevSingleL s k (harmonicSphereRotation k i j u)) =
    sphereSobolevRotationL s i j (sphereSobolevSingleL s k u) := by
    rw [sphereSobolevInclusionL_single,sphereSobolevRotationL_single]
  rw [he] at hd
  exact hd

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.contDiff_sphereSobolevOrthogonalPullback_coordinate_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_single_zero
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationL_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_single_lower_zero
