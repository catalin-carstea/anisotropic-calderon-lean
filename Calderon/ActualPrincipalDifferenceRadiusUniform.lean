import Calderon.ActualDensitySigmaMixedCoefficient
import Calderon.ActualPhysicalPureAngular
import Calderon.ActualHorizontalGeometry
import Calderon.CoordinateBootstrapJets
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError ConformalDepth ActualPhysicalPureAngular
  ActualPhysicalMixedNative ActualHorizontalNormBridge CoordinateBootstrapJets
  ReferenceDensityBounds NormalizedPrincipalMetric
attribute [local irreducible] referenceDensityPrincipalFrameCoefficient
  physicalMixedFrameCoefficient physicalPureAngularCoefficient referenceNormalizedPrincipalDifference

theorem principal_frame_difference_div_referenceRadius_eq_physicalPureAngularCoefficient
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (L q delta Rstar : ℝ) (p : ℕ) (y : R3) (i j : Fin 3) :
    (referenceDensityPrincipalFrameCoefficient g g2 L q y i j-(if i=j then (1:ℝ) else 0)) /
      referenceRadius delta Rstar p L y =
      physicalPureAngularCoefficient g L q delta Rstar p
        (referenceNormalizedPrincipalDifference g g2 L q) i j y := by
  rw [referenceDensityPrincipalFrameCoefficient_sub_kronecker_eq_physicalMixedFrameCoefficient
    g g2 hg L q y i j]
  simp only [physicalMixedFrameCoefficient,physicalPureAngularCoefficient,Fin.sum_univ_three,div_eq_mul_inv]
  ring

theorem exists_uniform_principal_frame_difference_div_radius_bound
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ q ∈ Icc (0:ℝ) 1,
      ∀ delta : ℝ, 0 < delta → ∀ Rstar : ℝ, 0 < Rstar →
      ∀ (p : ℕ) (eps : ℝ), 0 ≤ eps → ∀ y ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) y ≤
        eps*referenceRadius delta Rstar p L y → ∀ i j : Fin 3,
      |(referenceDensityPrincipalFrameCoefficient g g2 L q y i j-(if i=j then (1:ℝ) else 0)) /
        referenceRadius delta Rstar p L y| ≤ C0*eps := by
  obtain ⟨M,hM,hGeom⟩ := exists_reference_geometry_uniform_bounds g hg L K hK
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let C0 := 9*M^2+1
  have hC0 : 1 ≤ C0 := by dsimp [C0]; nlinarith [sq_nonneg M]
  refine ⟨C0,hC0,?_⟩
  intro q hq delta hdelta Rstar hRstar p eps heps y hy hBootstrap i j
  have hEntries (k l : Fin 3) :
      |referenceNormalizedPrincipalDifference g g2 L q y k l| ≤
        eps*referenceRadius delta Rstar p L y := by
    have h := abs_component_partial_le_H8 zeroMultiIndex
      (referenceNormalizedPrincipalDifference g g2 L q) y
      (by rw [multiIndexOrder_zero]; norm_num) k l
    simpa only [canonicalCoordinatePartial_zero] using h.trans hBootstrap
  have hFrame := (hGeom q hq y hy).2.1
  rw [principal_frame_difference_div_referenceRadius_eq_physicalPureAngularCoefficient g g2 hg]
  have hBound := physicalPureAngularCoefficient_bound g L q delta Rstar p
    (referenceNormalizedPrincipalDifference g g2 L q) hdelta hRstar y eps M
    heps hM0 hEntries hFrame i j
  exact hBound.trans (mul_le_mul_of_nonneg_right (by dsimp [C0]; linarith) heps)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
