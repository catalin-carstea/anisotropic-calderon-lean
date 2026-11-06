import Calderon.HarmonicCoordinateCompatibility
import Calderon.SphereDerivativeAdjoint

set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open AngularPolynomial SphereHarmonic HarmonicCoordinateCompatibility SphereDerivativeAdjoint

lemma coordinateHarmonicRaising_mem_all_degrees
    (k : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    coordinateHarmonicRaising k i p ∈ harmonicHomogeneous (k+1) := by
  cases k with
  | zero =>
    rw [eq_C_of_harmonicHomogeneous_zero p hp]
    simp only [coordinateHarmonicRaising,pderiv_C,mul_zero,sub_zero]
    refine ⟨?_,?_⟩
    · simpa using (isHomogeneous_X (R := ℝ) i).mul (isHomogeneous_C (Fin 3) (p.coeff 0))
    · rw [laplacian_X_mul]
      simp [laplacian]
  | succ k =>
    exact coordinateHarmonicRaising_harmonicHomogeneous (k+1) (by omega) i p hp

lemma pderiv_harmonicHomogeneous_pred
    (k : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    pderiv i p ∈ harmonicHomogeneous (k-1) := by
  cases k with
  | zero =>
    rw [eq_C_of_harmonicHomogeneous_zero p hp,pderiv_C]
    exact (harmonicHomogeneous (0-1)).zero_mem
  | succ k =>
    simpa only [Nat.add_sub_cancel] using pderiv_harmonicHomogeneous_succ k i p hp

lemma coordinateHarmonicProduct_defect_polynomial
    (k : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    coordinateHarmonicRaising k i p + C ((2*(k:ℝ)+1)⁻¹)*pderiv i p - X i*p =
      (1-radiusSq)*(C ((2*(k:ℝ)+1)⁻¹)*pderiv i p) := by
  unfold coordinateHarmonicRaising
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateHarmonicRaising_mem_all_degrees
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.pderiv_harmonicHomogeneous_pred
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateHarmonicProduct_defect_polynomial
