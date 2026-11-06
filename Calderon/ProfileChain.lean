import Calderon.RadiusProfileBounds
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr

namespace OAI.AnisotropicCalderon.RadiusProfile

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def logProfile (δ c : ℝ) (p : ℕ) (t : E → ℝ) (x : E) : ℝ :=
  c + (p : ℝ) * Real.log (softplus δ (t x))

noncomputable def profileDifferential (δ : ℝ) (p : ℕ) (t : E → ℝ)
    (x : E) : E →L[ℝ] ℝ :=
  ((p : ℝ) * logSlope δ (t x)) • fderiv ℝ t x

noncomputable def profileSecondDifferential (δ : ℝ) (p : ℕ) (t : E → ℝ)
    (x : E) (T : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ)) :
    E →L[ℝ] (E →L[ℝ] ℝ) :=
  ((p : ℝ) * logSlope δ (t x)) • H +
    (((p : ℝ) * logSlopeDerivative δ (t x)) • T).smulRight T

theorem hasFDerivAt_logProfile (δ c : ℝ) (p : ℕ) (t : E → ℝ)
    (x : E) (T : E →L[ℝ] ℝ) (hδ : 0 < δ) (ht : HasFDerivAt t T x) :
    HasFDerivAt (logProfile δ c p t) (((p : ℝ) * logSlope δ (t x)) • T) x := by
  have h := ((hasDerivAt_log_softplus δ (t x) hδ).comp_hasFDerivAt x ht).const_smul (p : ℝ)
  have hc := h.const_add c
  convert! hc using 1 <;>
    simp only [logProfile, Function.comp_apply, Pi.smul_apply, smul_eq_mul, smul_smul]

theorem fderiv_logProfile (δ c : ℝ) (p : ℕ) (t : E → ℝ)
    (x : E) (hδ : 0 < δ) (ht : DifferentiableAt ℝ t x) :
    fderiv ℝ (logProfile δ c p t) x = profileDifferential δ p t x :=
  (hasFDerivAt_logProfile δ c p t x (fderiv ℝ t x) hδ ht.hasFDerivAt).fderiv

theorem hasFDerivAt_profileDifferential (δ : ℝ) (p : ℕ) (t : E → ℝ)
    (x : E) (T : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ))
    (hδ : 0 < δ) (ht : HasFDerivAt t T x)
    (hH : HasFDerivAt (fderiv ℝ t) H x) :
    HasFDerivAt (profileDifferential δ p t)
      (profileSecondDifferential δ p t x T H) x := by
  have ha := ((hasDerivAt_logSlope δ (t x) hδ).comp_hasFDerivAt x ht).const_smul (p : ℝ)
  have h := ha.smul hH
  rw [ht.fderiv] at h
  convert! h using 1 <;>
    simp only [profileDifferential, profileSecondDifferential, Function.comp_apply,
      Pi.smul_apply, smul_eq_mul, smul_smul]

theorem hasFDerivAt_fderiv_logProfile (δ c : ℝ) (p : ℕ) (t : E → ℝ)
    (x : E) (T : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ))
    (hδ : 0 < δ) (ht : HasFDerivAt t T x)
    (hH : HasFDerivAt (fderiv ℝ t) H x)
    (hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ t y) :
    HasFDerivAt (fderiv ℝ (logProfile δ c p t))
      (profileSecondDifferential δ p t x T H) x := by
  apply (hasFDerivAt_profileDifferential δ p t x T H hδ ht hH).congr_of_eventuallyEq
  filter_upwards [hnear] with y hy
  exact fderiv_logProfile δ c p t y hδ hy

noncomputable def coordinateHessian (u : E → ℝ) (Γ : E → E → E)
    (x X Y : E) : ℝ :=
  fderiv ℝ (fderiv ℝ u) x X Y - fderiv ℝ u x (Γ X Y)

theorem coordinateHessian_logProfile (δ c : ℝ) (p : ℕ) (t : E → ℝ)
    (Γ : E → E → E) (x : E) (T : E →L[ℝ] ℝ)
    (H : E →L[ℝ] (E →L[ℝ] ℝ)) (hδ : 0 < δ)
    (ht : HasFDerivAt t T x) (hH : HasFDerivAt (fderiv ℝ t) H x)
    (hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ t y) (X Y : E) :
    coordinateHessian (logProfile δ c p t) Γ x X Y =
      profileHessianForm δ (t x) p (coordinateHessian t Γ x) T X Y := by
  have hfirst := (hasFDerivAt_logProfile δ c p t x T hδ ht).fderiv
  have hsecond := (hasFDerivAt_fderiv_logProfile δ c p t x T H hδ ht hH hnear).fderiv
  unfold coordinateHessian profileHessianForm
  rw [hfirst, hsecond, ht.fderiv, hH.fderiv]
  simp only [profileSecondDifferential, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem coordinateHessian_logProfile_le (δ c ct C : ℝ) (p : ℕ) (t : E → ℝ)
    (Γ : E → E → E) (x : E) (T : E →L[ℝ] ℝ)
    (H : E →L[ℝ] (E →L[ℝ] ℝ)) (hδ : 0 < δ)
    (ht : HasFDerivAt t T x) (hH : HasFDerivAt (fderiv ℝ t) H x)
    (hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ t y)
    (hct : 0 ≤ ct) (hC : 0 < C) (hT : ‖T‖ ≤ C)
    (hdepth : ∀ X, coordinateHessian t Γ x X X ≤ -ct * ‖X‖^2) (X : E) :
    coordinateHessian (logProfile δ c p t) Γ x X X ≤
      -(ct/C)*((p : ℝ)*logSlope δ (t x)*‖T‖)*‖X‖^2 := by
  rw [coordinateHessian_logProfile δ c p t Γ x T H hδ ht hH hnear]
  exact profileHessianForm_le δ (t x) ct C p (coordinateHessian t Γ x) T
    hδ hct hC hT hdepth X

#print axioms hasFDerivAt_fderiv_logProfile
#print axioms coordinateHessian_logProfile
#print axioms coordinateHessian_logProfile_le
end OAI.AnisotropicCalderon.RadiusProfile
