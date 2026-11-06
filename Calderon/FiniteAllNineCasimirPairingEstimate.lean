import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.RotationCasimirEstimate

/-! Full upfront expansion: EXPANSION-v001.json. Genuine finite vector pairing
bookkeeping only; actual physical Csharp construction remains a separate obligation. -/

lemma abs_sum_real_inner_le_sqrt_sum_norm_sq
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : ι → E) :
    |∑ i : ι, ⟪x i,y i⟫_ℝ| ≤
      Real.sqrt (∑ i : ι, ‖x i‖^2) * Real.sqrt (∑ i : ι, ‖y i‖^2) := by
  calc
    _ ≤ ∑ i : ι, |⟪x i,y i⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, ‖x i‖ * ‖y i‖ :=
      Finset.sum_le_sum (fun i _ => abs_real_inner_le_norm (x i) (y i))
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖x i‖) (fun i => ‖y i‖)

lemma abs_half_sum_nine_inner_sub_inner_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B ru rv : Fin 3 × Fin 3 → E) (M0 Mstar U V : ℝ)
    (hM0 : 0 ≤ M0) (hMstar : 0 ≤ Mstar) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hA : ∀ ij, ‖A ij‖ ≤ 2*M0*U) (hB : ∀ ij, ‖B ij‖ ≤ 2*Mstar*V)
    (hru : (∑ ij : Fin 3 × Fin 3, ‖ru ij‖^2) ≤ 2*U^2)
    (hrv : (∑ ij : Fin 3 × Fin 3, ‖rv ij‖^2) ≤ 2*V^2) :
    |(1/2:ℝ) * (∑ ij : Fin 3 × Fin 3,
      (⟪A ij,rv ij⟫_ℝ - ⟪ru ij,B ij⟫_ℝ))| ≤
      3*Real.sqrt 2*(M0+Mstar)*U*V := by
  have hAsq : (∑ ij : Fin 3 × Fin 3, ‖A ij‖^2) ≤ 9*(2*M0*U)^2 := by
    calc
      _ ≤ ∑ ij : Fin 3 × Fin 3, (2*M0*U)^2 := by
        apply Finset.sum_le_sum
        intro ij _
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hA ij)
      _ = _ := by simp
  have hBsq : (∑ ij : Fin 3 × Fin 3, ‖B ij‖^2) ≤ 9*(2*Mstar*V)^2 := by
    calc
      _ ≤ ∑ ij : Fin 3 × Fin 3, (2*Mstar*V)^2 := by
        apply Finset.sum_le_sum
        intro ij _
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hB ij)
      _ = _ := by simp
  have hsqrtA : Real.sqrt (∑ ij : Fin 3 × Fin 3, ‖A ij‖^2) ≤ 6*M0*U :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [hAsq]⟩
  have hsqrtB : Real.sqrt (∑ ij : Fin 3 × Fin 3, ‖B ij‖^2) ≤ 6*Mstar*V :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [hBsq]⟩
  have hsqrt2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtru : Real.sqrt (∑ ij : Fin 3 × Fin 3, ‖ru ij‖^2) ≤ Real.sqrt 2*U := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, hsqrt2]
    exact hru
  have hsqrtrv : Real.sqrt (∑ ij : Fin 3 × Fin 3, ‖rv ij‖^2) ≤ Real.sqrt 2*V := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, hsqrt2]
    exact hrv
  have hFirst : |∑ ij : Fin 3 × Fin 3, ⟪A ij,rv ij⟫_ℝ| ≤
      (6*M0*U)*(Real.sqrt 2*V) :=
    (abs_sum_real_inner_le_sqrt_sum_norm_sq A rv).trans
      (mul_le_mul hsqrtA hsqrtrv (Real.sqrt_nonneg _) (by positivity))
  have hSecond : |∑ ij : Fin 3 × Fin 3, ⟪ru ij,B ij⟫_ℝ| ≤
      (Real.sqrt 2*U)*(6*Mstar*V) :=
    (abs_sum_real_inner_le_sqrt_sum_norm_sq ru B).trans
      (mul_le_mul hsqrtru hsqrtB (Real.sqrt_nonneg _) (by positivity))
  calc
    _ = (1/2:ℝ) * |(∑ ij : Fin 3 × Fin 3, ⟪A ij,rv ij⟫_ℝ) -
        ∑ ij : Fin 3 × Fin 3, ⟪ru ij,B ij⟫_ℝ| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), Finset.sum_sub_distrib]
    _ ≤ (1/2:ℝ) * (|∑ ij : Fin 3 × Fin 3, ⟪A ij,rv ij⟫_ℝ| +
        |∑ ij : Fin 3 × Fin 3, ⟪ru ij,B ij⟫_ℝ|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    _ ≤ (1/2:ℝ) * ((6*M0*U)*(Real.sqrt 2*V) +
        (Real.sqrt 2*U)*(6*Mstar*V)) :=
      mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) (by norm_num)
    _ = _ := by ring

#print axioms OAI.AnisotropicCalderon.RotationCasimirEstimate.abs_sum_real_inner_le_sqrt_sum_norm_sq
#print axioms OAI.AnisotropicCalderon.RotationCasimirEstimate.abs_half_sum_nine_inner_sub_inner_le

end OAI.AnisotropicCalderon.RotationCasimirEstimate
