import Calderon.SphereSobolevRotationOrbitDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation SmoothSphereRotationProjection DirichletFamily.DriftBootstrap

/-! Distribution differentiation uses the actual one-order-loss rotation theorem. -/

lemma sphereSobolevRotationL_inclusion (s t : ℝ) (hts : t ≤ s) (i j : Fin 3) :
    (sphereSobolevRotationL t i j).comp (sphereSobolevInclusionL s t hts) =
    (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (sphereSobolevRotationL s i j) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext (t-1)
  intro k
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_rotation,
    sphereSobolevCoefficientL_inclusion]

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevRotationL
  sphereSobolevOrthogonalPullbackL coordinateRotationIsometry

lemma sphereSobolevInclusionL_eq_of_order_eq_conormal
    (s t r : ℝ) (ht : t ≤ s) (hr : r ≤ s) (htr : t = r) :
    sphereSobolevInclusionL s t ht = sphereSobolevInclusionL s r hr := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  rw [sphereSobolevInclusionL_apply, sphereSobolevInclusionL_apply, htr]

lemma clm_covariance_derivative_unique_conormal
    {U V W : Type*} [NormedAddCommGroup U] [NormedAddCommGroup V]
    [NormedAddCommGroup W] [NormedSpace ℝ U] [NormedSpace ℝ V] [NormedSpace ℝ W]
    (Q : ℝ → U →L[ℝ] V) (Q₀ C : U →L[ℝ] V)
    (hQ : HasDerivAt Q C 0) (hzero : Q 0 = Q₀)
    (u : ℝ → U) (u₀ u₁ : U) (hu : HasDerivAt u u₁ 0) (hu₀ : u 0 = u₀)
    (I : V →L[ℝ] W) (z : ℝ → W) (z₁ : W) (hz : HasDerivAt z z₁ 0)
    (hcurve : ∀ θ, z θ = I (Q θ (u θ))) :
    z₁ = I (C u₀ + Q₀ u₁) := by
  have hLeft := hQ.clm_apply hu
  rw [hu₀, hzero] at hLeft
  have hIncluded := I.hasFDerivAt.comp_hasDerivAt 0 hLeft
  have hSame := hIncluded.congr_of_eventuallyEq
    (Filter.Eventually.of_forall hcurve)
  exact hz.unique hSame

lemma sphereSobolevConormal_rotation_derivative_distribution
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i j : Fin 3)
    (Q : ℝ → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Q₀ C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hQ : HasDerivAt Q C 0) (hzero : Q 0 = Q₀)
    (hcov : ∀ θ f, Q θ (sphereSobolevOrthogonalPullbackL (1/2:ℝ)
      (coordinateRotationIsometry i j θ) f) =
      sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ) (Q₀ f))
    (f : SphereSobolev (3/2:ℝ)) :
    sphereSobolevRotationL (-(1/2:ℝ)) i j
      (Q₀ (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) =
    sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
      (C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) +
        Q₀ (sphereSobolevRotationL (3/2:ℝ) i j f)) := by
  have hInput := hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower_zero
    hO hD (3/2:ℝ) i j f
  have hInputOrder : (3/2:ℝ)-1 = (1/2:ℝ) := by norm_num
  have hInputInclusion := sphereSobolevInclusionL_eq_of_order_eq_conormal
    (3/2:ℝ) ((3/2:ℝ)-1) (1/2:ℝ) (by norm_num) (by norm_num) hInputOrder
  have hInputNormalized := hInput.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun θ =>
      ((congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T f)
        (sphereSobolevInclusionL_orthogonalPullback (3/2:ℝ) (1/2:ℝ) (by norm_num)
          (coordinateRotationIsometry i j θ))).symm).trans
        (congrArg (fun T => T (sphereSobolevOrthogonalPullbackL (3/2:ℝ)
          (coordinateRotationIsometry i j θ) f)) hInputInclusion.symm)))
  have hRight := hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower_zero hO hD
    (-(1/2:ℝ)) i j (Q₀ (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f))
  have hOutputOrder : (-(1/2:ℝ))-1 = -(3/2:ℝ) := by norm_num
  have hOutputInclusion := sphereSobolevInclusionL_eq_of_order_eq_conormal
    (-(1/2:ℝ)) ((-(1/2:ℝ))-1) (-(3/2:ℝ)) (by norm_num) (by norm_num) hOutputOrder
  have hRightNormalized := hRight.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun θ =>
      (congrArg (fun T => T (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ))
        (coordinateRotationIsometry i j θ)
        (Q₀ (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f))))
        hOutputInclusion).symm))
  exact clm_covariance_derivative_unique_conormal Q Q₀ C hQ hzero
    (fun θ => sphereSobolevOrthogonalPullbackL (1/2:ℝ)
      (coordinateRotationIsometry i j θ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
    (sphereSobolevRotationL (3/2:ℝ) i j f) hInputNormalized
    (sphereSobolevOrthogonalPullback_coordinate_zero (1/2:ℝ) i j _)
    (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num))
    (fun θ => sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ)
        (Q₀ (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f))))
    (sphereSobolevRotationL (-(1/2:ℝ)) i j
      (Q₀ (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f))) hRightNormalized
    (fun θ => (congrArg (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num))
      (hcov θ (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f))).symm)

lemma sphereSobolevConormal_rotation_derivative_graph_agreement
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i j : Fin 3)
    (Q : ℝ → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Q₀ C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hQ : HasDerivAt Q C 0) (hzero : Q 0 = Q₀)
    (hcov : ∀ θ f, Q θ (sphereSobolevOrthogonalPullbackL (1/2:ℝ)
      (coordinateRotationIsometry i j θ) f) =
      sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ) (Q₀ f))
    (f : SphereSobolev (3/2:ℝ)) (y : SphereSobolev (1/2:ℝ))
    (hy : Q₀ (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) y) :
    C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevRotationL (1/2:ℝ) i j y - Q₀ (sphereSobolevRotationL (3/2:ℝ) i j f) := by
  have h := sphereSobolevConormal_rotation_derivative_distribution hO hD i j Q Q₀ C hQ hzero hcov f
  have hcompat : sphereSobolevRotationL (-(1/2:ℝ)) i j
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) y) =
    sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
      (sphereSobolevRotationL (1/2:ℝ) i j y) := by
    have hc := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev ((-(1/2:ℝ))-1) => T y)
      (sphereSobolevRotationL_inclusion (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) i j)
    simp only [ContinuousLinearMap.comp_apply] at hc
    have hInclusion : sphereSobolevInclusionL ((1/2:ℝ)-1) ((-(1/2:ℝ))-1) (by norm_num) =
        sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) := by
      congr 1 <;> norm_num
    rw [hInclusion] at hc
    exact hc
  have hOutput := congrArg (sphereSobolevRotationL (-(1/2:ℝ)) i j) hy
  have hGraph := hcompat.symm.trans (hOutput.symm.trans h)
  have hAlg := sphereSobolevInclusionL_injective (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) hGraph
  exact eq_sub_iff_add_eq.mpr hAlg.symm

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationL_inclusion
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevConormal_rotation_derivative_distribution
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevConormal_rotation_derivative_graph_agreement

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_eq_of_order_eq_conormal

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.clm_covariance_derivative_unique_conormal
