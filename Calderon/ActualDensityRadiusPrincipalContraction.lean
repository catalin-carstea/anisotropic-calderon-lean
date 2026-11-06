import Calderon.ActualDensityPrincipalDiagonalSplit

/-! Radius contraction of the principal part: signed-radius algebra only. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

lemma smul_inv_add_inv_sq_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r a : ℝ) (hr : r ≠ 0) (x z : E) :
    r • (a • (r⁻¹ • x + (r⁻¹)^2 • z)) = a • x + r⁻¹ • (a • z) := by
  have hOne : r * (a * r⁻¹) = a := by
    calc
      r * (a * r⁻¹) = a * (r * r⁻¹) := by ring
      _ = a := by rw [mul_inv_cancel₀ hr, mul_one]
  have hTwo : r * (a * (r⁻¹)^2) = r⁻¹ * a := by
    calc
      r * (a * (r⁻¹)^2) = (r * r⁻¹) * (r⁻¹ * a) := by ring
      _ = r⁻¹ * a := by rw [mul_inv_cancel₀ hr, one_mul]
  simp only [smul_add, smul_smul, hOne, hTwo]

attribute [local irreducible] referenceDensityPrincipalFrameCoefficient
  sphereSobolevAngularCoordinateTransposeL

lemma sum_referenceDensityPrincipalFrameCoefficient_radius_angular_part
    (g g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (L q : ℝ) (y : R3)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (r : ℝ) (hr : r ≠ 0) (D : Fin 3 → SphereSobolev (1/2 : ℝ))
    (u : SphereSobolev (3/2 : ℝ)) :
    r • (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        (r⁻¹ • (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j) +
          sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j (D i)) +
        (r⁻¹)^2 • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
          (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u))) =
    (2 : ℝ) • (∑ i : Fin 3, sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D i)) +
    (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3,
      (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
        if i = j then (1 : ℝ) else 0) •
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j)) +
    r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3,
      (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
        if i = j then (1 : ℝ) else 0) •
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u)) := by
  classical
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let A := sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ)
  let Ah := sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)
  have hScale (i j : Fin 3) :
      r • (Q i j • (r⁻¹ • (A i (D j) + A j (D i)) + (r⁻¹)^2 • A i (Ah j u))) =
      Q i j • (A i (D j) + A j (D i)) + r⁻¹ • (Q i j • A i (Ah j u)) :=
    smul_inv_add_inv_sq_smul r (Q i j) hr (A i (D j) + A j (D i)) (A i (Ah j u))
  have hSum :
      r • (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j • (r⁻¹ • (A i (D j) + A j (D i)) + (r⁻¹)^2 • A i (Ah j u))) =
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (A i (D j) + A j (D i))) +
      r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • A i (Ah j u)) := by
    simp only [Finset.smul_sum]
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (Q i j • (A i (D j) + A j (D i)) + r⁻¹ • (Q i j • A i (Ah j u))) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hScale i j))
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hCross := sum_referenceDensityPrincipalFrameCoefficient_angularTranspose_cross
    g g2 hg2 L q y hF hO hD D
  have hDiag := sum_referenceDensityPrincipalFrameCoefficient_angularTranspose_eq_diagonal_add
    g g2 L q y hF hO hD D
  have hDouble := sum_referenceDensityPrincipalFrameCoefficient_angularTranspose_twice
    g g2 L q y hF hO hD u
  have hCrossSplit := hCross.trans (congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) => (2 : ℝ) • z) hDiag)
  have hCrossFinal := hCrossSplit.trans
    (smul_add (2 : ℝ)
      (∑ i : Fin 3, A i (D i))
      (∑ i : Fin 3, ∑ j : Fin 3,
        (Q i j - if i = j then (1 : ℝ) else 0) • A i (D j)))
  exact hSum.trans (congrArg₂
    (fun x z : SphereSobolev (-(1/2 : ℝ)) => x + r⁻¹ • z)
    hCrossFinal hDouble)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smul_inv_add_inv_sq_smul
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_referenceDensityPrincipalFrameCoefficient_radius_angular_part
