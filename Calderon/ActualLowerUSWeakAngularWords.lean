import Calderon.ActualPiMixedWeakEndpointCore

/-!
Author: GPT-6.1 Sol, author support only.
Before-code: ../lower-r-z-upfront.md.
Only the two concrete typed word constructors needed for actual R/Z.
Their arguments are operator coefficients, not hypotheses supplying analytic caps.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSWeakAngularWords
open SphereHarmonic ActualAngularPiDraft
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "NegHi" => SphereSobolev (-(3/2 : ℝ))

/-- Actual two-factor angular word in its ordinary bounded endpoint. -/
def angularTwoWord (B : Half →L[ℝ] Neg) (C : Hi →L[ℝ] Half) : Hi →L[ℝ] Neg :=
  B.comp C

lemma norm_angularTwoWord_le (B : Half →L[ℝ] Neg) (C : Hi →L[ℝ] Half) :
    ‖angularTwoWord B C‖ ≤ ‖B‖*‖C‖ :=
  ContinuousLinearMap.opNorm_comp_le B C

/-- A three-factor weak word, with the actual left adjoint already on the test.
No angular operator is applied to a negative Sobolev output. -/
def angularThreeWordWeak (Asharp : Hi →L[ℝ] Half)
    (B : Half →L[ℝ] Neg) (C : Hi →L[ℝ] Half) : Hi →L[ℝ] NegHi :=
  (v016TransposeL Asharp).comp (angularTwoWord B C)

lemma angularThreeWordWeak_pairing (Asharp : Hi →L[ℝ] Half)
    (B : Half →L[ℝ] Neg) (C : Hi →L[ℝ] Half) (u v : Hi) :
    sphereSobolevDualPairing (3/2 : ℝ) u (angularThreeWordWeak Asharp B C v) =
      sphereSobolevDualPairing (1/2 : ℝ) (Asharp u) (B (C v)) :=
  v016TransposeL_pairing Asharp (B (C v)) u

lemma norm_angularThreeWordWeak_le (Asharp : Hi →L[ℝ] Half)
    (B : Half →L[ℝ] Neg) (C : Hi →L[ℝ] Half) :
    ‖angularThreeWordWeak Asharp B C‖ ≤ ‖Asharp‖*‖B‖*‖C‖ := by
  calc
    _ ≤ ‖v016TransposeL Asharp‖*‖angularTwoWord B C‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Asharp‖*(‖B‖*‖C‖) := mul_le_mul
      (norm_v016TransposeL_apply_le Asharp) (norm_angularTwoWord_le B C)
      (norm_nonneg (angularTwoWord B C)) (norm_nonneg Asharp)
    _ = _ := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSWeakAngularWords
