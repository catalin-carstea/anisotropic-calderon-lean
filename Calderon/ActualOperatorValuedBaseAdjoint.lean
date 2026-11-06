import Calderon.AngularEuclideanDensity
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.ActualOperatorValuedBaseAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def baseDirectionalDeriv (v : R3) (u : R3 → E) : R3 → E :=
  fun x => fderiv ℝ u x v

lemma contDiff_baseDirectionalDeriv (v : R3) (u : R3 → E)
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (baseDirectionalDeriv v u) := by
  exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma hasCompactSupport_baseDirectionalDeriv (v : R3) (u : R3 → E)
    (hc : HasCompactSupport u) : HasCompactSupport (baseDirectionalDeriv v u) := by
  exact hc.fderiv_apply (𝕜 := ℝ) v

lemma compact_inner_integrable (f g : R3 → E) (hf : Continuous f)
    (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun x => ⟪f x, g x⟫_ℝ) := by
  apply (hf.inner hg).integrable_of_hasCompactSupport
  apply hc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp [hx]

lemma compact_inner_baseDirectionalDeriv (v : R3) (f g : R3 → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    (∫ x : R3, ⟪f x, baseDirectionalDeriv v g x⟫_ℝ) =
      -(∫ x : R3, ⟪baseDirectionalDeriv v f x, g x⟫_ℝ) := by
  apply integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := innerSL ℝ (E := E))
  · exact compact_inner_integrable _ g
      (contDiff_baseDirectionalDeriv v f hf).continuous hg.continuous hc
  · exact compact_inner_integrable f _ hf.continuous
      (contDiff_baseDirectionalDeriv v g hg).continuous
      (hasCompactSupport_baseDirectionalDeriv v g hc)
  · exact compact_inner_integrable f g hf.continuous hg.continuous hc
  · intro x _
    exact hf.differentiable (by simp) x
  · intro x _
    exact hg.differentiable (by simp) x

/-- One genuine base integration by parts for an operator-valued coefficient.
    The exact density remains within the derivative on the adjoint side. -/
theorem compact_operator_second_one_parts
    (i j : R3) (mu : R3 → ℝ) (A : R3 → E →L[ℝ] E)
    (u w q : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hu : ContDiff ℝ ∞ u)
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport u)
    (hpair : ∀ x z, ⟪A x z, w x⟫_ℝ = ⟪z, q x⟫_ℝ) :
    (∫ x : R3, mu x *
      ⟪A x (baseDirectionalDeriv i (baseDirectionalDeriv j u) x), w x⟫_ℝ) =
      -(∫ x : R3, ⟪baseDirectionalDeriv i (fun y => mu y • q y) x,
        baseDirectionalDeriv j u x⟫_ℝ) := by
  have hparts := compact_inner_baseDirectionalDeriv i
    (fun y => mu y • q y) (baseDirectionalDeriv j u)
    (hm.smul hq) (contDiff_baseDirectionalDeriv j u hu)
    (hasCompactSupport_baseDirectionalDeriv j u hc)
  convert hparts using 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hpair]
  simp only [real_inner_smul_left, real_inner_comm]

end OAI.AnisotropicCalderon.ActualOperatorValuedBaseAdjoint
