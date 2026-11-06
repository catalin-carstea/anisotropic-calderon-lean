import Calderon.SphereSobolevSingleRotationAngleDerivative
import Calderon.UniformContractiveFamilyConvergence

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation DirichletFamily.DriftBootstrap

/-! Strong continuity is for each fixed datum, without infinite-space angle operator-norm continuity. -/

lemma norm_sphereSobolevOrthogonalPullback_partialSum_tail (s : ℝ) (i j : Fin 3)
    (u : SphereSobolev s) (n : ℕ) (θ : ℝ) :
    ‖sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u -
      sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) (sphereSobolevPartialSum s n u)‖ =
      ‖u-sphereSobolevPartialSum s n u‖ := by
  rw [← map_sub,norm_sphereSobolevOrthogonalPullbackL_apply]

lemma tendstoUniformly_sphereSobolevOrthogonalPullback_partialSum (s : ℝ) (i j : Fin 3)
    (u : SphereSobolev s) :
    TendstoUniformly (fun n θ => sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
      (sphereSobolevPartialSum s n u))
      (fun θ => sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u) atTop := by
  apply tendstoUniformly_contractive_family_apply
  · intro θ v
    exact (norm_sphereSobolevOrthogonalPullbackL_apply s (coordinateRotationIsometry i j θ) v).le
  · exact tendsto_sphereSobolevPartialSum s u

lemma continuous_sphereSobolevOrthogonalPullback_coordinate_partialSum
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ)
    (i j : Fin 3) (u : SphereSobolev s) (n : ℕ) :
    Continuous (fun θ => sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
      (sphereSobolevPartialSum s n u)) := by
  simp only [sphereSobolevPartialSum,map_sum]
  exact continuous_finsetSum (Finset.range n) (fun k hk =>
    (contDiff_sphereSobolevOrthogonalPullback_coordinate_single hO hD s i j k
      (sphereSobolevCoefficientL s k u)).continuous)

lemma continuous_sphereSobolevOrthogonalPullback_coordinate
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ)
    (i j : Fin 3) (u : SphereSobolev s) :
    Continuous (fun θ => sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u) := by
  apply (tendstoUniformly_sphereSobolevOrthogonalPullback_partialSum s i j u).continuous
  exact (Filter.Eventually.of_forall (fun n =>
    continuous_sphereSobolevOrthogonalPullback_coordinate_partialSum hO hD s i j u n)).frequently

lemma sphereSobolevOrthogonalPullback_coordinate_zero (s : ℝ) (i j : Fin 3) (u : SphereSobolev s) :
    sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j 0) u = u := by
  apply sphereSobolev_ext s
  intro k
  rw [sphereSobolevCoefficientL_orthogonalPullback,harmonicSphereOrthogonalPullback_coordinate_zero]

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevOrthogonalPullback_partialSum_tail
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.tendstoUniformly_sphereSobolevOrthogonalPullback_partialSum
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.continuous_sphereSobolevOrthogonalPullback_coordinate_partialSum
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.continuous_sphereSobolevOrthogonalPullback_coordinate
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevOrthogonalPullback_coordinate_zero
