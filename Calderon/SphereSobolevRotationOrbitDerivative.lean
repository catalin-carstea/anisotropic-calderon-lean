import Calderon.SphereSobolevRotationStrongContinuity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation SmoothSphereRotationProjection DirichletFamily.DriftBootstrap

/-! The true orbit loses exactly one order when differentiated; norm-smoothness of R_s as an operator is not asserted. -/

lemma hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_partialSum_lower
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ)
    (i j : Fin 3) (u : SphereSobolev s) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun θ => sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
        (sphereSobolevPartialSum s n u)))
      (sphereSobolevOrthogonalPullbackL (s-1) (coordinateRotationIsometry i j t)
        (sphereSobolevRotationL s i j (sphereSobolevPartialSum s n u))) t := by
  simp only [sphereSobolevPartialSum,map_sum,sphereSobolevRotationL_single,
    sphereSobolevOrthogonalPullbackL_single,sphereSobolevInclusionL_single]
  apply HasDerivAt.fun_sum
  intro k hk
  exact (sphereSobolevSingleL (s-1) k).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_harmonicSphereOrthogonalPullback_coordinate hO hD i j k
      (sphereSobolevCoefficientL s k u) t)

lemma norm_sphereSobolevRotationOrbit_derivative_partialSum_tail (s : ℝ) (i j : Fin 3)
    (u : SphereSobolev s) (n : ℕ) (θ : ℝ) :
    ‖sphereSobolevOrthogonalPullbackL (s-1) (coordinateRotationIsometry i j θ) (sphereSobolevRotationL s i j u) -
      sphereSobolevOrthogonalPullbackL (s-1) (coordinateRotationIsometry i j θ)
        (sphereSobolevRotationL s i j (sphereSobolevPartialSum s n u))‖ =
      ‖sphereSobolevRotationL s i j (u-sphereSobolevPartialSum s n u)‖ := by
  rw [← map_sub,norm_sphereSobolevOrthogonalPullbackL_apply,← map_sub]

lemma tendstoUniformly_sphereSobolevRotationOrbit_partialSum_derivative (s : ℝ)
    (i j : Fin 3) (u : SphereSobolev s) :
    TendstoUniformly (fun n θ => sphereSobolevOrthogonalPullbackL (s-1) (coordinateRotationIsometry i j θ)
      (sphereSobolevRotationL s i j (sphereSobolevPartialSum s n u)))
      (fun θ => sphereSobolevOrthogonalPullbackL (s-1) (coordinateRotationIsometry i j θ)
        (sphereSobolevRotationL s i j u)) atTop := by
  apply tendstoUniformly_contractive_family_apply
  · intro θ v
    exact (norm_sphereSobolevOrthogonalPullbackL_apply (s-1) (coordinateRotationIsometry i j θ) v).le
  · exact ((sphereSobolevRotationL s i j).continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)

lemma tendsto_sphereSobolevOrthogonalPullback_coordinate_partialSum_lower
    (s : ℝ) (i j : Fin 3) (u : SphereSobolev s) (θ : ℝ) :
    Tendsto (fun n => sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
        (sphereSobolevPartialSum s n u))) atTop
      (𝓝 (sphereSobolevInclusionL s (s-1) (by linarith)
        (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u))) := by
  have hR := ((sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)).continuous.tendsto u).comp
    (tendsto_sphereSobolevPartialSum s u)
  exact ((sphereSobolevInclusionL s (s-1) (by linarith)).continuous.tendsto
    (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u)).comp hR

lemma hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ)
    (i j : Fin 3) (u : SphereSobolev s) (t : ℝ) :
    HasDerivAt (fun θ => sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u))
      (sphereSobolevOrthogonalPullbackL (s-1) (coordinateRotationIsometry i j t)
        (sphereSobolevRotationL s i j u)) t := by
  apply hasDerivAt_of_tendstoUniformly
    (g := fun θ => sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u))
    (g' := fun θ => sphereSobolevOrthogonalPullbackL (s-1) (coordinateRotationIsometry i j θ)
      (sphereSobolevRotationL s i j u)) (x := t)
    (f := fun n θ => sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
        (sphereSobolevPartialSum s n u)))
    (f' := fun n θ => sphereSobolevOrthogonalPullbackL (s-1) (coordinateRotationIsometry i j θ)
      (sphereSobolevRotationL s i j (sphereSobolevPartialSum s n u))) (l := atTop)
  · exact tendstoUniformly_sphereSobolevRotationOrbit_partialSum_derivative s i j u
  · exact Filter.Eventually.of_forall (fun n θ =>
      hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_partialSum_lower hO hD s i j u n θ)
  · intro θ
    exact tendsto_sphereSobolevOrthogonalPullback_coordinate_partialSum_lower s i j u θ

lemma hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower_zero
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ)
    (i j : Fin 3) (u : SphereSobolev s) :
    HasDerivAt (fun θ => sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u))
      (sphereSobolevRotationL s i j u) 0 := by
  have h := hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower hO hD s i j u 0
  rw [sphereSobolevOrthogonalPullback_coordinate_zero] at h
  exact h

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_partialSum_lower
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevRotationOrbit_derivative_partialSum_tail
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.tendstoUniformly_sphereSobolevRotationOrbit_partialSum_derivative
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.tendsto_sphereSobolevOrthogonalPullback_coordinate_partialSum_lower
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower_zero
