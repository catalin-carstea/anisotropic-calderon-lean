import Calderon.ActualHigherSQuadraticZeroWords
set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
open ActualHigherSQuadraticZeroWords
lemma contDiff_wordCoefficient_of_components {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E → ℝ) (Q : E → Fin 3 → Fin 3 → ℝ)
    (f : E → Fin 3 → ℝ) (Γ : E → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hR : ContDiff ℝ ∞ R) (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j))
    (hf : ∀ i, ContDiff ℝ ∞ (fun x => f x i))
    (hΓ : ∀ i a b, ContDiff ℝ ∞ (fun x => Γ x i a b)) (z : ZeroWord) :
    ContDiff ℝ ∞ (fun x => wordCoefficient (R x) (Q x) (f x) (Γ x) z) := by
  rcases z with ⟨⟨i,j⟩, kind⟩
  cases kind with
  | inl ab => exact (((hR.pow 2).div_const 2).mul (hQ i j)).mul (hΓ i ab.1 ab.2)
  | inr kind =>
    cases kind with
    | inl ab => exact (((hR.pow 2).div_const 2).mul (hQ i j)).mul (hΓ j ab.1 ab.2)
    | inr m =>
      simp only [wordCoefficient]
      split_ifs
      · exact ((hR.pow 2).mul (hQ i j)).mul (hf i)
      · exact ((hR.pow 2).mul (hQ i j)).mul (hf j)
      · exact hR.mul (hQ i j)
      · exact hR.mul (hQ i j)
      · exact (hR.pow 3).mul (hQ i j)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
