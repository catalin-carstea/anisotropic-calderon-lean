import Calderon.RadiusTwoNativeSourceFoundation
import TauCeti.Analysis.Sobolev.W1p.Multiplication

/-! EXPANSION.json precedes the focused actual smooth-cutoff native jet identity. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource

theorem radiusTwoSmoothCutoff_jetField_ae
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient χ x‖ ≤ M) (u : RadiusTwoH1) :
    TauCeti.PDE.jetField (TauCeti.W1p.contDiffSMulL χ hχ hM hAbs hGrad u)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      (fun x => χ x • TauCeti.PDE.jetField u x +
        TauCeti.W1p.value u x • ((0 : ℝ),gradient χ x)) := by
  rw [TauCeti.W1p.contDiffSMulL_apply]
  filter_upwards [TauCeti.W1p.value_contDiffSMul_ae hχ hM hAbs hGrad u,
    TauCeti.W1p.gradient_contDiffSMul_ae hχ hM hAbs hGrad u] with x hv hg
  rw [TauCeti.PDE.jetField_apply,hv,hg,TauCeti.PDE.jetField_apply]
  simp only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,mul_zero,add_zero]

end OAI.AnisotropicCalderon.ExteriorSource
