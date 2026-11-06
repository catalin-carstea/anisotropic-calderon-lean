import Calderon.ActualOperatorValuedBaseAdjoint

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.ActualOperatorValuedBaseAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma contDiff_adjoint_apply (A : R3 → E →L[ℝ] E) (w : R3 → E)
    (hA : ContDiff ℝ ∞ A) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x => (ContinuousLinearMap.adjoint (A x)) (w x)) := by
  have hadj : ContDiff ℝ ∞ (ContinuousLinearMap.adjoint :
      (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E)) :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E)).contDiff
  exact (hadj.comp hA).clm_apply hw

theorem compact_operator_second_one_parts_adjoint
    (i j : R3) (mu : R3 → ℝ) (A : R3 → E →L[ℝ] E)
    (u w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hA : ContDiff ℝ ∞ A)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport u) :
    (∫ x : R3, mu x *
      ⟪A x (baseDirectionalDeriv i (baseDirectionalDeriv j u) x), w x⟫_ℝ) =
      -(∫ x : R3, ⟪baseDirectionalDeriv i
        (fun y => mu y • (ContinuousLinearMap.adjoint (A y)) (w y)) x,
        baseDirectionalDeriv j u x⟫_ℝ) := by
  apply compact_operator_second_one_parts i j mu A u w
    (fun x => (ContinuousLinearMap.adjoint (A x)) (w x)) hm hu
    (contDiff_adjoint_apply A w hA hw) hc
  intro x z
  exact (ContinuousLinearMap.adjoint_inner_right (A x) z (w x)).symm

end OAI.AnisotropicCalderon.ActualOperatorValuedBaseAdjoint
