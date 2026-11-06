import Calderon.ActualReferenceDDHigherGeometryJets
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ActualReferenceDDHigherGeometryJets
open ReferenceDensityBounds

/-- The original ordered coordinate words obey exact scalar pullback. -/
lemma coordinateFieldWordPartial_comp_const_smul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : List (Fin 3)) (f : R3 → V) (c : ℝ) (x : R3) :
    coordinateFieldWordPartial w (fun y => f (c • y)) x =
      c ^ w.length • coordinateFieldWordPartial w f (c • x) := by
  induction w generalizing x with
  | nil => simp only [coordinateFieldWordPartial, List.length_nil, pow_zero, one_smul]
  | cons k w ih =>
      have hFunction : coordinateFieldWordPartial w (fun y => f (c • y)) =
          (c ^ w.length) • (fun y => coordinateFieldWordPartial w f (c • y)) := by
        funext y
        exact ih y
      have hScalar : fderiv ℝ
          ((c ^ w.length) • (fun y => coordinateFieldWordPartial w f (c • y))) x =
          (c ^ w.length) • fderiv ℝ
            (fun y => coordinateFieldWordPartial w f (c • y)) x :=
        congrFun (fderiv_const_smul_field (𝕜 := ℝ)
          (f := fun y => coordinateFieldWordPartial w f (c • y)) (c ^ w.length)) x
      have hScale : fderiv ℝ (fun y => coordinateFieldWordPartial w f (c • y)) x =
          c • fderiv ℝ (coordinateFieldWordPartial w f) (c • x) :=
        fderiv_comp_smul (𝕜 := ℝ) (f := coordinateFieldWordPartial w f) (x := x) c
      have hDerivative : fderiv ℝ
          ((c ^ w.length) • (fun y => coordinateFieldWordPartial w f (c • y))) x =
          (c ^ (w.length + 1)) • fderiv ℝ (coordinateFieldWordPartial w f) (c • x) := by
        rw [hScalar, hScale, smul_smul, pow_succ]
      change fderiv ℝ (coordinateFieldWordPartial w (fun y => f (c • y))) x
          (coordinateDirection k) =
        (c ^ (w.length + 1)) •
          (fderiv ℝ (coordinateFieldWordPartial w f) (c • x) (coordinateDirection k))
      rw [hFunction]
      simpa only [ContinuousLinearMap.smul_apply] using
        congrArg (fun A : R3 →L[ℝ] V => A (coordinateDirection k)) hDerivative

/-- Passing from radius one to radius two does not enlarge a word bound. -/
lemma norm_coordinateFieldWordPartial_le_dilated
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : List (Fin 3)) (f : R3 → V) (z : R3) :
    ‖coordinateFieldWordPartial w f z‖ ≤
      ‖coordinateFieldWordPartial w (fun y => f ((2 : ℝ) • y)) ((2 : ℝ)⁻¹ • z)‖ := by
  have hPoint : (2 : ℝ) • ((2 : ℝ)⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  have hValue := coordinateFieldWordPartial_comp_const_smul w f (2 : ℝ) ((2 : ℝ)⁻¹ • z)
  rw [hPoint] at hValue
  have hNorm :
      ‖coordinateFieldWordPartial w (fun y => f ((2 : ℝ) • y)) ((2 : ℝ)⁻¹ • z)‖ =
        (2 : ℝ) ^ w.length * ‖coordinateFieldWordPartial w f z‖ := by
    rw [hValue, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) w.length)]
  have hPow : (1 : ℝ) ≤ (2 : ℝ) ^ w.length := one_le_pow₀ (by norm_num)
  exact (le_mul_of_one_le_left (norm_nonneg _) hPow).trans_eq hNorm.symm

end OAI.AnisotropicCalderon.ActualReferenceDDHigherGeometryJets

#print axioms OAI.AnisotropicCalderon.ActualReferenceDDHigherGeometryJets.coordinateFieldWordPartial_comp_const_smul
#print axioms OAI.AnisotropicCalderon.ActualReferenceDDHigherGeometryJets.norm_coordinateFieldWordPartial_le_dilated
