import Calderon.ActualConstantOneDoubleRaisingHalfLift
import Calderon.ActualPrincipalDifferenceRadiusUniform
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic EnergyBridge ConnectionError ConformalDepth ReferenceDensityBounds
  ActualPhysicalPureAngular CoordinateBootstrapJets NormalizedPrincipalMetric

/-- The actual principal-difference forcing on literal one, lifted to the required output space. -/
def constantOnePrincipalDifferenceHalf (hF : SphereFischerInner)
    (g g2 : MatrixField) (L q delta Rstar : ℝ) (p : ℕ) (y : R3) : SphereSobolev (1/2:ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ((referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
      (if i=j then (1:ℝ) else 0)) / referenceRadius delta Rstar p L y) •
      constantOneDoubleRaisingHalf hF i j

theorem sphereSobolevInclusionL_constantOnePrincipalDifferenceHalf
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (L q delta Rstar : ℝ) (p : ℕ) (y : R3) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (constantOnePrincipalDifferenceHalf hF g g2 L q delta Rstar p y) =
    (referenceRadius delta Rstar p L y)⁻¹ •
      (∑ i : Fin 3, ∑ j : Fin 3,
        (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
          (if i=j then (1:ℝ) else 0)) •
          sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2:ℝ) i
            (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2:ℝ) j
              (sphereSobolevConstantOne (3/2:ℝ)))) := by
  rw [constantOnePrincipalDifferenceHalf,
    sphereSobolevInclusionL_sum_constantOneDoubleRaisingHalf hF hO hD]
  simp only [Finset.smul_sum,div_eq_mul_inv,smul_smul,mul_comm]

theorem exists_uniform_constantOnePrincipalDifferenceHalf_bound
    (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ Icc (0:ℝ) 1,
      ∀ delta : ℝ, 0 < delta → ∀ Rstar : ℝ, 0 < Rstar →
      ∀ (p : ℕ) (eps : ℝ), 0 ≤ eps → ∀ y ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) y ≤
        eps*referenceRadius delta Rstar p L y →
      ‖constantOnePrincipalDifferenceHalf hF g g2 L q delta Rstar p y‖ ≤ C*eps := by
  obtain ⟨C0,hC0,hCoeffs⟩ :=
    exists_uniform_principal_frame_difference_div_radius_bound g g2 hg L K hK
  obtain ⟨M,hM,hNorm⟩ := exists_constantOneDoubleRaisingHalf_sum_norm_bound hF
  have hC00 : 0 ≤ C0 := zero_le_one.trans hC0
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  refine ⟨M*C0+1,by nlinarith [mul_nonneg hM0 hC00],?_⟩
  intro q hq delta hdelta Rstar hRstar p eps heps y hy hBootstrap
  have h := hNorm
    (fun i j => (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
      (if i=j then (1:ℝ) else 0)) / referenceRadius delta Rstar p L y)
    (C0*eps) (mul_nonneg hC00 heps)
    (hCoeffs q hq delta hdelta Rstar hRstar p eps heps y hy hBootstrap)
  change ‖constantOnePrincipalDifferenceHalf hF g g2 L q delta Rstar p y‖ ≤ M*(C0*eps) at h
  exact h.trans (by nlinarith only [heps])

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
