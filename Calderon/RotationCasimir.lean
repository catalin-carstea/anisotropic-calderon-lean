import Calderon.SphereDerivativeAdjoint
import Calderon.SphereRotationCore

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.RotationCasimir
open AngularPolynomial SphereHarmonic SphereDerivativeAdjoint

def polynomialEuler (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, X i * pderiv i p

def polynomialCasimir (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  C (-(1/2 : ℝ)) * ∑ i : Fin 3, ∑ j : Fin 3,
    polynomialRotation i j (polynomialRotation i j p)

theorem sum_double_rotation_eq (p : MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, polynomialRotation i j (polynomialRotation i j p)) =
      2 * (radiusSq * laplacian p - polynomialEuler (polynomialEuler p) - polynomialEuler p) := by
  simp [polynomialRotation,polynomialEuler,radiusSq,laplacian,Fin.sum_univ_three,
    pderiv_mul,pderiv_X]
  ring

lemma polynomialEuler_C_mul (a : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialEuler (C a * p) = C a * polynomialEuler p := by
  simp [polynomialEuler,Finset.mul_sum,mul_left_comm,mul_assoc]

lemma polynomialEuler_homogeneous (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous k) : polynomialEuler p = C (k:ℝ) * p := by
  simpa [polynomialEuler,nsmul_eq_mul] using hp.sum_X_mul_pderiv

theorem polynomialCasimir_harmonic (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) : polynomialCasimir p = C ((k:ℝ)*((k:ℝ)+1)) * p := by
  rw [polynomialCasimir,sum_double_rotation_eq,polynomialEuler_homogeneous k p hp.1,
    polynomialEuler_C_mul,polynomialEuler_homogeneous k p hp.1,hp.2]
  have he : 2 * ((radiusSq : MvPolynomial (Fin 3) ℝ) * 0 -
      C (k:ℝ) * (C (k:ℝ)*p) - C (k:ℝ)*p) =
      C (-(2*(k:ℝ)*((k:ℝ)+1))) * p := by
    simp only [map_neg,map_mul,map_add,map_ofNat,map_one]
    ring
  rw [he,← mul_assoc,← map_mul]
  apply congrArg (fun a : ℝ => C a * p)
  ring

lemma polynomialRotation_harmonic_all (k : ℕ) (i j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    polynomialRotation i j p ∈ harmonicHomogeneous k := by
  cases k with
  | zero =>
      rw [eq_C_of_harmonicHomogeneous_zero p hp]
      simp only [polynomialRotation,pderiv_C,mul_zero,sub_self]
      exact (harmonicHomogeneous 0).zero_mem
  | succ k => exact polynomialRotation_harmonicHomogeneous _ (by omega) i j p hp

lemma polynomialRotation_sphere_inner_skew_all (hF : SphereFischerInner)
    (k : ℕ) (i j : Fin 3) (p q : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) (hq : q ∈ harmonicHomogeneous k) :
    ⟪polynomialSphereL2 (polynomialRotation i j p),polynomialSphereL2 q⟫_ℝ =
      -⟪polynomialSphereL2 p,polynomialSphereL2 (polynomialRotation i j q)⟫_ℝ := by
  cases k with
  | zero =>
      rw [eq_C_of_harmonicHomogeneous_zero p hp,eq_C_of_harmonicHomogeneous_zero q hq]
      simp [polynomialRotation]
  | succ k => exact polynomialRotation_sphere_inner_skew hF _ (by omega) i j p q hp hq

theorem sum_rotation_sphere_norm_sq (hF : SphereFischerInner)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    (∑ i : Fin 3, ∑ j : Fin 3, ‖polynomialSphereL2 (polynomialRotation i j p)‖^2) =
      (2*(k:ℝ)*((k:ℝ)+1))*‖polynomialSphereL2 p‖^2 := by
  have hterm (i j : Fin 3) :
      ‖polynomialSphereL2 (polynomialRotation i j p)‖^2 =
        -⟪polynomialSphereL2 p,
          polynomialSphereL2 (polynomialRotation i j (polynomialRotation i j p))⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    exact polynomialRotation_sphere_inner_skew_all hF k i j p _ hp
      (polynomialRotation_harmonic_all k i j p hp)
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

end OAI.AnisotropicCalderon.RotationCasimir
