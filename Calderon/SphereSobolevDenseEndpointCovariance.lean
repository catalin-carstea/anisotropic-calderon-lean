import Calderon.SphereSobolevCoordinateOrthogonalCovariance

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma denseRange_clm_apply_eq
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (I : X →L[ℝ] Y) (hI : DenseRange I) (L R : Y →L[ℝ] Z)
    (h : ∀ x, L (I x) = R (I x)) (y : Y) : L y = R y := by
  exact hI.induction_on y (isClosed_eq L.continuous R.continuous) h

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevOrthogonalPullbackL

lemma lowerEndpoint_orthogonal_covariance_of_upper
    (e : R3 ≃ₗᵢ[ℝ] R3)
    (A B : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (C D : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : ∀ f, A (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (C f))
    (hB : ∀ f, B (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (D f))
    (hD : ∀ f, D (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f) =
      sphereSobolevOrthogonalPullbackL (1/2:ℝ) e (C f))
    (f : SphereSobolev (1/2:ℝ)) :
    B (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e f) =
      sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e (A f) := by
  apply denseRange_clm_apply_eq
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (B.comp (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e))
    ((sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e).comp A)
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hInput := sphereSobolevInclusionL_orthogonalPullback_apply
    (3/2:ℝ) (1/2:ℝ) (by norm_num) e u
  have hOutput := sphereSobolevInclusionL_orthogonalPullback_apply
    (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) e (C u)
  exact (congrArg B hInput.symm).trans ((hB _).trans
    ((congrArg (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) (hD u)).trans
      (hOutput.trans (congrArg (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e) (hA u).symm))))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.lowerEndpoint_orthogonal_covariance_of_upper

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.denseRange_clm_apply_eq
