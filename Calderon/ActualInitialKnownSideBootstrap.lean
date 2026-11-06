import Calderon.ActualPhysicalKnownBallParameterOrderedTransfer
import Calderon.ActualNormalizedPrincipalH8InitialSmallness
import Calderon.ActualHigherRadiusProfile

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ConformalDepth RadiusProfile ReferenceWeightedApproximation
  ActualHigherRadiusProfile ActualNormalizedPrincipalH8InitialSmallness
  CoordinateBootstrapJets ActualScalarPrincipalAdjoint

theorem radius_beta_square_mono_of_positive_scale
    (g : MatrixField) (L lam delta Rsmall Rbig : ℝ) (p : ℕ)
    (hdelta : 0 < delta) (hSmall : 0 < Rsmall) (hBig : 0 < Rbig)
    (hScale : Rsmall ≤ Rbig) (y : R3) :
    referenceRadius delta Rsmall p L y * (actualReferenceBeta g L lam delta Rsmall p y) ^ 2 ≤
      referenceRadius delta Rbig p L y * (actualReferenceBeta g L lam delta Rbig p y) ^ 2 := by
  rw [actualReferenceBeta_eq g L lam delta Rsmall p hdelta hSmall y,
    actualReferenceBeta_eq g L lam delta Rbig p hdelta hBig y]
  unfold referenceRadius
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hScale (pow_nonneg (softplus_pos delta _ hdelta).le p))
    (sq_nonneg _)

theorem exists_initial_known_side_current_radius_bootstrap
    (S : KnownSideSourceData) (L : ℝ) (hL : 0 < L) :
    ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
      ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ 1 ∧
        ∀ lam ∈ Icc (0 : ℝ) lam0,
          CurrentRadiusBootstrap S L lam 1 Rstar eps p := by
  obtain ⟨p0,_,hp02,hAllocate⟩ :=
    exists_fixed_actual_reference_beta_power_radius_profile S.g1 S.g1_admissible L hL
      cylinder isCompact_native_center_cylinder 2
  refine ⟨p0,hp02,?_⟩
  intro p hp eps heps heps1
  obtain ⟨R0,hR0,hProfile⟩ := hAllocate p hp eps heps heps1
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRstar hRstar0
  have hRadius : Continuous (referenceRadius 1 Rstar p L) :=
    (contDiff_referenceRadius_actual 1 Rstar p L zero_lt_one hRstar).continuous
  have hNonempty : cylinder.Nonempty := by
    refine ⟨0,?_⟩
    change ((0 : R3) 0) ^ 2 + ((0 : R3) 1) ^ 2 ≤ 1 ∧
      (-1 : ℝ) ≤ (0 : R3) 2 ∧ (0 : R3) 2 ≤ 1
    norm_num
  obtain ⟨y0,hy0,hMinimum⟩ :=
    isCompact_native_center_cylinder.exists_isMinOn hNonempty hRadius.continuousOn
  have hMinPositive : 0 < referenceRadius 1 Rstar p L y0 :=
    referenceRadius_pos 1 Rstar p L y0 zero_lt_one hRstar
  obtain ⟨lam0,hlam0,hlam01,hSmall⟩ :=
    exists_referenceNormalizedPrincipalDifference_coordinateH8_small S.g1 S.g2
      S.g1_admissible S.g2_admissible S.g1_origin S.g2_origin L
      cylinder isCompact_native_center_cylinder
      (eps * referenceRadius 1 Rstar p L y0) (mul_pos heps hMinPositive)
  refine ⟨lam0,hlam0,hlam01,?_⟩
  intro lam hlam
  constructor
  · intro y hy
    exact (hSmall lam hlam y hy).trans
      (mul_le_mul_of_nonneg_left (isMinOn_iff.mp hMinimum y hy) heps.le)
  · intro delta' hdelta' y hy
    have hDelta : delta' = 1 := le_antisymm hdelta'.2 hdelta'.1
    subst delta'
    have hAtR0 := (hProfile lam ⟨hlam.1,hlam.2.trans hlam01⟩ 1 zero_lt_one le_rfl y hy).2.1
    exact (radius_beta_square_mono_of_positive_scale S.g1 L lam 1 Rstar R0 p
      zero_lt_one hRstar hR0 hRstar0 y).trans hAtR0

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
