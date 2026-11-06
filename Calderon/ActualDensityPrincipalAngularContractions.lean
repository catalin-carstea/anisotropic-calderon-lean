import Calderon.ActualDensityPrincipalFrameSymmetry
import Calderon.ActualNativeLeadingAngularCancellation

/-! Actual native angular endpoints. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceDensityPrincipalFrameCoefficient
  sphereSobolevAngularCoordinateTransposeL

lemma sum_referenceDensityPrincipalFrameCoefficient_angularTranspose_cross
    (g g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (L q : ℝ) (y : R3)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (D : Fin 3 → SphereSobolev (1/2 : ℝ)) :
    (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j) +
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j (D i))) =
    (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j)) := by
  have hSwap :
      (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j (D i)) =
      (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [referenceDensityPrincipalFrameCoefficient_symm g g2 hg2 L q y j i]
  simp only [smul_add, Finset.sum_add_distrib, hSwap, two_smul ℝ]

lemma sum_referenceDensityPrincipalFrameCoefficient_angularTranspose_twice
    (g g2 : MatrixField) (L q : ℝ) (y : R3)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (u : SphereSobolev (3/2 : ℝ)) :
    (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u)) =
    (∑ i : Fin 3, ∑ j : Fin 3,
      (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
        if i = j then (1 : ℝ) else 0) •
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u)) := by
  classical
  have hDiag : (∑ i : Fin 3, ∑ j : Fin 3, (if i = j then (1 : ℝ) else 0) •
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u)) = 0 := by
    simpa using sum_sphereSobolevAngularCoordinateTranspose_twice_eq_zero hF hO hD u
  simp only [sub_smul, Finset.sum_sub_distrib, hDiag, sub_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_referenceDensityPrincipalFrameCoefficient_angularTranspose_cross
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_referenceDensityPrincipalFrameCoefficient_angularTranspose_twice
