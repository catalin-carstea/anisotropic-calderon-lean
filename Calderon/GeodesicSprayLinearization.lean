import Calderon.SmoothGeodesicFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def zeroVelocityLinearization : (E × E) →L[ℝ] E × E :=
  (ContinuousLinearMap.snd ℝ E E).prod (0 : (E × E) →L[ℝ] E)

theorem zeroVelocityLinearization_apply (w : E × E) :
    zeroVelocityLinearization w = (w.2,0) := rfl

theorem zeroVelocityLinearization_nilpotent (w : E × E) :
    zeroVelocityLinearization (zeroVelocityLinearization w) = 0 := rfl

variable [CompleteSpace E]

theorem hasFDerivAt_geodesicPhaseField_zero_velocity (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (y : E) :
    HasFDerivAt (geodesicPhaseField Q M) zeroVelocityLinearization (y,0) := by
  have hg : ContDiff ℝ ∞ (fun p : E × E => coordinateConnectionField Q M p.1) :=
    (contDiff_coordinateConnectionField_infty Q M hQ hM).comp contDiff_fst
  have hΓ := (hg.differentiable (by simp) (y,0)).hasFDerivAt
  have hV : HasFDerivAt (fun p : E × E => p.2)
      (ContinuousLinearMap.snd ℝ E E) (y,0) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have hR := (hΓ.clm_apply hV).clm_apply hV
  have hR0 : HasFDerivAt
      (fun p : E × E => coordinateConnectionField Q M p.1 p.2 p.2)
      (0 : (E × E) →L[ℝ] E) (y,0) := by
    simpa using hR
  convert hV.prodMk hR0.neg using 1 <;>
    simp [zeroVelocityLinearization]
  funext p
  rfl

theorem fderiv_geodesicPhaseField_zero_velocity (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (y : E) :
    fderiv ℝ (geodesicPhaseField Q M) (y,0) = zeroVelocityLinearization :=
  (hasFDerivAt_geodesicPhaseField_zero_velocity Q M hQ hM y).fderiv

theorem fderiv_geodesicPhaseField_zero_velocity_nilpotent (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (y : E) (w : E × E) :
    fderiv ℝ (geodesicPhaseField Q M) (y,0)
      (fderiv ℝ (geodesicPhaseField Q M) (y,0) w) = 0 := by
  rw [fderiv_geodesicPhaseField_zero_velocity Q M hQ hM y]
  exact zeroVelocityLinearization_nilpotent w

end OAI.AnisotropicCalderon.ConnectionError
