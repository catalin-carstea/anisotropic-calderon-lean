import Calderon.SphereSobolevRotationOrbitDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation SmoothSphereRotationProjection DirichletFamily.DriftBootstrap

/-! Only near-zero finite covariance is needed; applications must derive it. -/

lemma sphereSobolev_operator_zero_of_eventually_coordinate_covariance
    (s t : ℝ) (i j : Fin 3)
    (Q : ℝ → SphereSobolev s →L[ℝ] SphereSobolev t)
    (Q₀ : SphereSobolev s →L[ℝ] SphereSobolev t)
    (hcov : ∀ᶠ θ in 𝓝 (0:ℝ), ∀ u : SphereSobolev s,
      Q θ (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u) =
      sphereSobolevOrthogonalPullbackL t (coordinateRotationIsometry i j θ) (Q₀ u)) :
    Q 0 = Q₀ := by
  apply ContinuousLinearMap.ext
  intro u
  have h := hcov.self_of_nhds u
  simpa only [sphereSobolevOrthogonalPullback_coordinate_zero] using h

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevRotationL
  sphereSobolevOrthogonalPullbackL coordinateRotationIsometry

lemma sphereSobolevInclusionL_eq_of_order_eq_local
    (s t r : ℝ) (ht : t ≤ s) (hr : r ≤ s) (htr : t = r) :
    sphereSobolevInclusionL s t ht = sphereSobolevInclusionL s r hr := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  rw [sphereSobolevInclusionL_apply, sphereSobolevInclusionL_apply, htr]

lemma clm_local_covariance_derivative_unique
    {U V W : Type*} [NormedAddCommGroup U] [NormedAddCommGroup V]
    [NormedAddCommGroup W] [NormedSpace ℝ U] [NormedSpace ℝ V] [NormedSpace ℝ W]
    (Q : ℝ → U →L[ℝ] V) (Q₀ C : U →L[ℝ] V)
    (hQ : HasDerivAt Q C 0) (hzero : Q 0 = Q₀)
    (u : ℝ → U) (u₀ u₁ : U) (hu : HasDerivAt u u₁ 0) (hu₀ : u 0 = u₀)
    (I : V →L[ℝ] W) (z : ℝ → W) (z₁ : W) (hz : HasDerivAt z z₁ 0)
    (hcurve : z =ᶠ[𝓝 (0:ℝ)] (fun θ => I (Q θ (u θ)))) :
    z₁ = I (C u₀ + Q₀ u₁) := by
  have hLeft := hQ.clm_apply hu
  rw [hu₀, hzero] at hLeft
  have hIncluded := I.hasFDerivAt.comp_hasDerivAt 0 hLeft
  have hSame := hIncluded.congr_of_eventuallyEq hcurve
  exact hz.unique hSame

lemma sphereSobolev_local_rotation_derivative_distribution
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (i j : Fin 3)
    (Q : ℝ → SphereSobolev s →L[ℝ] SphereSobolev t)
    (Q₀ C : SphereSobolev s →L[ℝ] SphereSobolev t)
    (hQ : HasDerivAt Q C 0)
    (hcov : ∀ᶠ θ in 𝓝 (0:ℝ), ∀ u : SphereSobolev s,
      Q θ (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) u) =
      sphereSobolevOrthogonalPullbackL t (coordinateRotationIsometry i j θ) (Q₀ u))
    (f : SphereSobolev (s+1)) :
    sphereSobolevRotationL t i j (Q₀ (sphereSobolevInclusionL (s+1) s (by linarith) f)) =
      sphereSobolevInclusionL t (t-1) (by linarith)
        (C (sphereSobolevInclusionL (s+1) s (by linarith) f) +
          Q₀ (sphereSobolevRotationL (s+1) i j f)) := by
  have hzero := sphereSobolev_operator_zero_of_eventually_coordinate_covariance s t i j Q Q₀ hcov
  have hInput := hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower_zero hO hD (s+1) i j f
  have hInputOrder : (s+1)-1 = s := by ring
  have hInputInclusion := sphereSobolevInclusionL_eq_of_order_eq_local
    (s+1) ((s+1)-1) s (by linarith) (by linarith) hInputOrder
  have hInputNormalized := hInput.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun θ =>
      ((congrArg (fun T : SphereSobolev (s+1) →L[ℝ] SphereSobolev s => T f)
        (sphereSobolevInclusionL_orthogonalPullback (s+1) s (by linarith)
          (coordinateRotationIsometry i j θ))).symm).trans
        (congrArg (fun T => T (sphereSobolevOrthogonalPullbackL (s+1)
          (coordinateRotationIsometry i j θ) f)) hInputInclusion.symm)))
  have hRight := hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower_zero hO hD t i j
    (Q₀ (sphereSobolevInclusionL (s+1) s (by linarith) f))
  exact clm_local_covariance_derivative_unique Q Q₀ C hQ hzero
    (fun θ => sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ)
      (sphereSobolevInclusionL (s+1) s (by linarith) f))
    (sphereSobolevInclusionL (s+1) s (by linarith) f)
    (sphereSobolevRotationL (s+1) i j f) hInputNormalized
    (sphereSobolevOrthogonalPullback_coordinate_zero s i j _)
    (sphereSobolevInclusionL t (t-1) (by linarith))
    (fun θ => sphereSobolevInclusionL t (t-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL t (coordinateRotationIsometry i j θ)
        (Q₀ (sphereSobolevInclusionL (s+1) s (by linarith) f))))
    (sphereSobolevRotationL t i j (Q₀ (sphereSobolevInclusionL (s+1) s (by linarith) f)))
    hRight (hcov.mono (fun θ hθ =>
      (congrArg (sphereSobolevInclusionL t (t-1) (by linarith))
        (hθ (sphereSobolevInclusionL (s+1) s (by linarith) f))).symm))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_operator_zero_of_eventually_coordinate_covariance
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_local_rotation_derivative_distribution

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_eq_of_order_eq_local

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.clm_local_covariance_derivative_unique
