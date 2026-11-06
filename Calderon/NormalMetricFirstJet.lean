import Calderon.NormalizedGeodesicMetric

set_option autoImplicit false
noncomputable section
open scoped ContDiff InnerProduct
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_radialEndpoint_zero (Θ : E × E → E) (y z : E)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0)) :
    HasDerivAt (fun r : ℝ => scaledEndpoint Θ ((y,r),z)) z 0 := by
  have hc : HasDerivAt (fun r : ℝ => (y,r • z)) (0,z) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) y).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const z)
  have hd := hD.comp_hasDerivAt_of_eq 0 hc (by simp)
  simpa [scaledEndpoint,Function.comp_def] using hd

theorem hasDerivAt_radialEndpointDerivative_zero (Θ : E × E → E)
    (hΘ : ContDiff ℝ ∞ Θ) (y z u : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hH : fderiv ℝ (fderiv ℝ Θ) (y,0) (0,z) (0,u) = -Γ z u) :
    HasDerivAt (fun r : ℝ => normalizedEndpointDerivative Θ ((y,r),z) u) (-Γ z u) 0 := by
  have hs : ContDiff ℝ ∞ (fderiv ℝ Θ) := hΘ.fderiv_right (by simp)
  have hd := (hs.differentiable (by simp) (y,0)).hasFDerivAt.clm_apply
    (hasFDerivAt_const (0,u) (y,(0 : E)))
  have hc : HasDerivAt (fun r : ℝ => (y,r • z)) (0,z) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) y).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const z)
  have hp := hd.comp_hasDerivAt_of_eq 0 hc (by simp)
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,map_zero,zero_add] at hp
  rw [hH] at hp
  simpa [normalizedEndpointDerivative,Function.comp_def] using hp

theorem hasDerivAt_normalizedEndpointMetric_inner_zero (Θ : E × E → E)
    (M : E → E →L[ℝ] E) (hΘ : ContDiff ℝ ∞ Θ) (hM : ContDiff ℝ ∞ M)
    (y z u v : E) (Γ : E →L[ℝ] E →L[ℝ] E) (hzero : Θ (y,0) = y)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0))
    (hH : ∀ z u : E, fderiv ℝ (fderiv ℝ Θ) (y,0) (0,z) (0,u) = -Γ z u)
    (hcompat : ∀ X Y Z : E,
      inner ℝ (M y (Γ X Y)) Z + inner ℝ (M y Y) (Γ X Z) =
        inner ℝ (fderiv ℝ M y X Y) Z) :
    HasDerivAt (fun r : ℝ => inner ℝ (normalizedEndpointMetric Θ M ((y,r),z) u) v) 0 0 := by
  have hX := hasDerivAt_radialEndpoint_zero Θ y z hD
  have hXu : scaledEndpoint Θ ((y,(0 : ℝ)),z) = y := scaledEndpoint_zero Θ y z hzero
  have hJu := hasDerivAt_radialEndpointDerivative_zero Θ hΘ y z u Γ (hH z u)
  have hJv := hasDerivAt_radialEndpointDerivative_zero Θ hΘ y z v Γ (hH z v)
  have hJ0 := normalizedEndpointDerivative_zero Θ y z hD
  have hMX := (hM.differentiable (by simp) y).hasFDerivAt.comp_hasDerivAt_of_eq 0 hX hXu.symm
  have hA := hMX.clm_apply hJu
  have hi := hA.inner ℝ hJv
  simp only [Function.comp_def,hXu,hJ0,ContinuousLinearMap.id_apply] at hi
  have hvalue : inner ℝ (M y u) (-Γ z v) + inner ℝ
      (fderiv ℝ M y z u + M y (-Γ z u)) v = 0 := by
    simp only [map_neg,inner_add_left,inner_neg_left,inner_neg_right]
    linarith [hcompat z u v]
  have he : (fun r : ℝ => inner ℝ (normalizedEndpointMetric Θ M ((y,r),z) u) v) =
      (fun r : ℝ => inner ℝ (M (scaledEndpoint Θ ((y,r),z))
        (normalizedEndpointDerivative Θ ((y,r),z) u))
        (normalizedEndpointDerivative Θ ((y,r),z) v)) := by
    funext r
    exact normalizedEndpointMetric_inner Θ M ((y,r),z) u v
  rw [he]
  rw [hvalue] at hi
  exact hi
end OAI.AnisotropicCalderon.ConnectionError
