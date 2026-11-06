import Calderon.RotationCasimir
import Calderon.SmoothSphereRotationProjection

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SmoothSphereRotationProjection AngularPolynomial RotationCasimir

/-! Actual harmonic vector Casimir, all nine ordered rotations, degree zero
included. No upper endpoint dependency. -/

lemma sum_harmonicSphereRotation_twice (k : ℕ) (v : harmonicSphereSubspace k) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      harmonicSphereRotation k i j (harmonicSphereRotation k i j v)) =
    (-(2*(k:ℝ)*((k:ℝ)+1))) • v := by
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨p,rfl⟩
  have hRot (i j : Fin 3) (q : harmonicHomogeneous k) :
      harmonicSphereRotation k i j (harmonicPolynomialSphereMap k q) =
      harmonicPolynomialSphereMap k
        ⟨polynomialRotation i j q,polynomialRotation_harmonic_all k i j q q.property⟩ := by
    rw [harmonicSphereRotation_apply_image]
    rfl
  simp only [hRot]
  apply Subtype.ext
  change (∑ i : Fin 3, ∑ j : Fin 3,
      polynomialSphereL2 (polynomialRotation i j (polynomialRotation i j p))) =
    (-(2*(k:ℝ)*((k:ℝ)+1))) • polynomialSphereL2 p
  simp_rw [← map_sum]
  rw [sum_double_rotation_eq,polynomialEuler_homogeneous k p p.property.1,
    polynomialEuler_C_mul,polynomialEuler_homogeneous k p p.property.1,p.property.2]
  have he : 2 * ((radiusSq : MvPolynomial (Fin 3) ℝ) * 0 -
      C (k:ℝ) * (C (k:ℝ)*(p : MvPolynomial (Fin 3) ℝ)) - C (k:ℝ)*(p : MvPolynomial (Fin 3) ℝ)) =
      C (-(2*(k:ℝ)*((k:ℝ)+1))) * (p : MvPolynomial (Fin 3) ℝ) := by
    simp only [map_neg,map_mul,map_add,map_ofNat,map_one]
    ring
  rw [he,← smul_eq_C_mul,map_smul]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_harmonicSphereRotation_twice
