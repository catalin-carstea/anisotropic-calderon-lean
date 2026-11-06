import Calderon.ActualDensityPrincipalAngularContractions

/-! Before-source: actual-physical-full-allocation-author-oct16-v001/
EXPANSION-principal-diagonal-split-v012.md. Actual identity/sigma leading split. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceDensityPrincipalFrameCoefficient
  sphereSobolevAngularCoordinateTransposeL

lemma sum_referenceDensityPrincipalFrameCoefficient_angularTranspose_eq_diagonal_add
    (g g2 : MatrixField) (L q : ℝ) (y : R3)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (D : Fin 3 → SphereSobolev (1/2 : ℝ)) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j)) =
    (∑ i : Fin 3, sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D i)) +
    (∑ i : Fin 3, ∑ j : Fin 3,
      (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
        if i = j then (1 : ℝ) else 0) •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j)) := by
  classical
  have hDiag : (∑ i : Fin 3, ∑ j : Fin 3, (if i = j then (1 : ℝ) else 0) •
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j)) =
      ∑ i : Fin 3, sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D i) := by
    simp
  rw [show (∑ i : Fin 3, ∑ j : Fin 3,
      (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
        if i = j then (1 : ℝ) else 0) •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j)) =
      (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j)) -
      (∑ i : Fin 3, sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D i)) by
    simp only [sub_smul, Finset.sum_sub_distrib, hDiag]]
  abel

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_referenceDensityPrincipalFrameCoefficient_angularTranspose_eq_diagonal_add
