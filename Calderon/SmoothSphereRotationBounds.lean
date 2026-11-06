import Calderon.SmoothSphereRotationProjection
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SmoothSphereRotationBounds
open SphereHarmonic AngularPolynomial RotationCasimir SmoothSphereRotationProjection

/-- Genuine probability rotation energy, using actual smooth skewness and no Fischer premise. -/
theorem sum_polynomialSphereL2_rotation_norm_sq (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    (∑ i : Fin 3, ∑ j : Fin 3, ‖polynomialSphereL2 (polynomialRotation i j p)‖^2) =
      (2*(k:ℝ)*((k:ℝ)+1))*‖polynomialSphereL2 p‖^2 := by
  have hterm (i j : Fin 3) :
      ‖polynomialSphereL2 (polynomialRotation i j p)‖^2 =
        -⟪polynomialSphereL2 p,
          polynomialSphereL2 (polynomialRotation i j (polynomialRotation i j p))⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    exact polynomialSphereL2_rotation_skew i j p (polynomialRotation i j p)
  simp_rw [hterm]
  simp_rw [Finset.sum_neg_distrib]
  simp_rw [← inner_sum,← map_sum]
  have hrot := sum_double_rotation_eq p
  rw [hrot,polynomialEuler_homogeneous k p hp.1,polynomialEuler_C_mul,
    polynomialEuler_homogeneous k p hp.1,hp.2]
  have he : 2 * ((radiusSq : MvPolynomial (Fin 3) ℝ) * 0 -
      C (k:ℝ) * (C (k:ℝ)*p) - C (k:ℝ)*p) =
      C (-(2*(k:ℝ)*((k:ℝ)+1))) * p := by
    simp only [map_neg,map_mul,map_add,map_ofNat,map_one]
    ring
  rw [he,← smul_eq_C_mul,map_smul,real_inner_smul_right,real_inner_self_eq_norm_sq]
  ring

theorem sum_harmonicSphereRotation_norm_sq (k : ℕ) (v : harmonicSphereSubspace k) :
    (∑ i : Fin 3, ∑ j : Fin 3, ‖harmonicSphereRotation k i j v‖^2) =
      (2*(k:ℝ)*((k:ℝ)+1))*‖v‖^2 := by
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨p,rfl⟩
  simp_rw [harmonicSphereRotation_apply_image]
  change (∑ i : Fin 3, ∑ j : Fin 3,
      ‖polynomialSphereL2 (polynomialRotation i j p)‖^2) =
    (2*(k:ℝ)*((k:ℝ)+1))*‖polynomialSphereL2 p‖^2
  exact sum_polynomialSphereL2_rotation_norm_sq k p p.property

lemma norm_harmonicSphereRotation_sq_le (k : ℕ) (i j : Fin 3)
    (v : harmonicSphereSubspace k) :
    ‖harmonicSphereRotation k i j v‖^2 ≤ (2*(k:ℝ)*((k:ℝ)+1))*‖v‖^2 := by
  rw [← sum_harmonicSphereRotation_norm_sq]
  exact (Finset.single_le_sum (fun a _ => sq_nonneg ‖harmonicSphereRotation k i a v‖)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ =>
      sq_nonneg ‖harmonicSphereRotation k a b v‖) (Finset.mem_univ i))

/-- Universal constant before every degree, pair, truncation, type and radius. -/
theorem norm_harmonicSphereRotation_le (k : ℕ) (i j : Fin 3)
    (v : harmonicSphereSubspace k) :
    ‖harmonicSphereRotation k i j v‖ ≤ Real.sqrt 2 * (1+(k:ℝ)) * ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hb := norm_harmonicSphereRotation_sq_le k i j v
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  rw [mul_pow,mul_pow,hs]
  have hk : (k:ℝ)*((k:ℝ)+1) ≤ (1+(k:ℝ))^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have he : 2*(k:ℝ)*((k:ℝ)+1) ≤ 2*(1+(k:ℝ))^2 := by nlinarith [hk]
  exact hb.trans (mul_le_mul_of_nonneg_right he (sq_nonneg ‖v‖))

end OAI.AnisotropicCalderon.SmoothSphereRotationBounds
