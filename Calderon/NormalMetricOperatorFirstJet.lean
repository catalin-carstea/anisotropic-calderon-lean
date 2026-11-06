import Calderon.NormalMetricFirstJet

set_option autoImplicit false
noncomputable section
open scoped ContDiff InnerProduct
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_normalizedEndpointMetric_zero (Θ : E × E → E)
    (M : E → E →L[ℝ] E) (hΘ : ContDiff ℝ ∞ Θ) (hM : ContDiff ℝ ∞ M)
    (y z : E) (Γ : E →L[ℝ] E →L[ℝ] E) (hzero : Θ (y,0) = y)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0))
    (hH : ∀ z u : E, fderiv ℝ (fderiv ℝ Θ) (y,0) (0,z) (0,u) = -Γ z u)
    (hcompat : ∀ X Y Z : E,
      inner ℝ (M y (Γ X Y)) Z + inner ℝ (M y Y) (Γ X Z) =
        inner ℝ (fderiv ℝ M y X Y) Z) :
    HasDerivAt (fun r : ℝ => normalizedEndpointMetric Θ M ((y,r),z)) 0 0 := by
  let H : ℝ → E →L[ℝ] E := fun r => normalizedEndpointMetric Θ M ((y,r),z)
  have hs : ContDiff ℝ ∞ H :=
    (contDiff_normalizedEndpointMetric Θ M hΘ hM).comp
      ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hd : HasDerivAt H (deriv H 0) 0 := (hs.differentiable (by simp) 0).hasDerivAt
  have hzeroD : deriv H 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    have he := (hd.clm_apply (hasDerivAt_const (0 : ℝ) u)).inner ℝ
      (hasDerivAt_const (0 : ℝ) v)
    have hi := hasDerivAt_normalizedEndpointMetric_inner_zero Θ M hΘ hM y z u v Γ
      hzero hD hH hcompat
    have hv := he.unique hi
    simpa using hv
  exact hd.congr_deriv hzeroD
end OAI.AnisotropicCalderon.ConnectionError
