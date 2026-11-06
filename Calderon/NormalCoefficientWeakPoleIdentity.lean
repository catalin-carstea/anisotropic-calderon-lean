import Calderon.RegularizedNormalCoefficientResidual
import Calderon.RegularizedInverseNormConvergence
import Calderon.SmoothPrincipalCompactTests
import Calderon.SmoothSymmetricPrincipalWeakPairing
import Calderon.NativeInverseNormFundamentalSolution
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily.DriftBootstrap NativePolynomialBulkMoments
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem continuous_regularizedNormalCoefficientRemainder
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (c0 t : ℝ) (ht : 0 < t) (p : P) :
    Continuous (regularizedNormalCoefficientRemainder a c0 t p) := by
  have haEntry (i j : Fin 3) : ContDiff ℝ ∞ (fun z : R3 => a (p,z) i j) :=
    ((normalResidualMatrixEntryL i j).contDiff.comp ha).comp (contDiff_const.prodMk contDiff_id)
  have hOne : matrixOperatorMap (1 : Matrix (Fin 3) (Fin 3) ℝ) = ContinuousLinearMap.id ℝ R3 := by
    change matrixOperatorAlgEquiv 1 = 1
    exact map_one matrixOperatorAlgEquiv
  have hGamma := contDiff_regularizedInverseNormPotential c0 t ht
  have hA := contDiff_neg_coordinateFluxDivergence_matrixGradient
    (fun z => a (p,z)) haEntry (regularizedInverseNormPotential c0 t) hGamma
  have hI := contDiff_neg_coordinateFluxDivergence_matrixGradient
    (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun _ _ => contDiff_const)
    (regularizedInverseNormPotential c0 t) hGamma
  simp only [hOne,ContinuousLinearMap.id_apply] at hI
  have hINeg : Continuous (fun z : R3 => -(-coordinateFluxDivergence
      (gradient (regularizedInverseNormPotential c0 t)) z)) := hI.continuous.neg
  simp only [neg_neg] at hINeg
  exact hA.continuous.add hINeg

theorem tendsto_integral_regularizedNormalCoefficientRemainder_mul_compact
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (p : P) (h0 : a (p,0) = 1) (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0)
    (c0 : ℝ) (φ : R3 → ℝ) (hφ : Continuous φ) (hCompact : HasCompactSupport φ) :
    Tendsto (fun t : ℝ => ∫ z : R3, regularizedNormalCoefficientRemainder a c0 t p z * φ z)
      (𝓝[>] 0) (𝓝 (∫ z : R3, normalCoefficientResidualProfile a c0 (p,z) * φ z)) := by
  let B : R3 → ℝ := fun z => normalCoefficientResidualAbsoluteCoefficient a (p,z)
  have hB : Continuous B := (continuous_normalCoefficientResidualAbsoluteCoefficient a ha).comp
    (continuous_const.prodMk continuous_id)
  have hWeight : Continuous (fun z => B z * |φ z|) := hB.mul hφ.abs
  have hWeightCompact : HasCompactSupport (fun z => B z * |φ z|) := hCompact.abs.mul_left
  have hMajorant : Integrable (fun z : R3 => inverseNormPotential |c0| z * (B z * |φ z|)) :=
    integrable_inverseNormPotential_mul_continuous_compact |c0| _ hWeight hWeightCompact
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : R3 => inverseNormPotential |c0| z * (B z * |φ z|))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((continuous_regularizedNormalCoefficientRemainder a ha c0 t ht p).mul hφ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [volume.ae_ne (0 : R3)] with z hz
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right
      (abs_regularizedNormalCoefficientRemainder_le a ha p h0 h1 c0 t ht z hz) (abs_nonneg (φ z))).trans_eq
      (by dsimp only [inverseNormPotential,B];ring)
  · exact hMajorant
  · filter_upwards [volume.ae_ne (0 : R3)] with z hz
    exact (tendsto_regularizedNormalCoefficientRemainder a ha p h0 h1 c0 z hz).mul_const (φ z)

theorem integral_regularizedInverseNormPotential_principal_split
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (p : P) (hSym : ∀ z : R3, (a (p,z)).IsSymm)
    (c0 t : ℝ) (ht : 0 < t) (φ : R3 → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hCompact : HasCompactSupport φ) :
    (∫ z : R3, regularizedInverseNormPotential c0 t z *
      (-coordinateFluxDivergence (fun x => matrixOperatorMap (a (p,x)) (gradient φ x)) z)) =
      (∫ z : R3, regularizedInverseNormPotential c0 t z * (-coordinateFluxDivergence (gradient φ) z)) +
      ∫ z : R3, regularizedNormalCoefficientRemainder a c0 t p z * φ z := by
  have haEntry (i j : Fin 3) : ContDiff ℝ ∞ (fun z : R3 => a (p,z) i j) :=
    ((normalResidualMatrixEntryL i j).contDiff.comp ha).comp (contDiff_const.prodMk contDiff_id)
  have hOne : matrixOperatorMap (1 : Matrix (Fin 3) (Fin 3) ℝ) = ContinuousLinearMap.id ℝ R3 := by
    change matrixOperatorAlgEquiv 1 = 1
    exact map_one matrixOperatorAlgEquiv
  have hGamma := contDiff_regularizedInverseNormPotential c0 t ht
  have hGA := integral_smooth_mul_neg_matrixGradient_divergence_symm
    (fun z => a (p,z)) haEntry (fun z i j => (hSym z).apply j i)
    (regularizedInverseNormPotential c0 t) φ hGamma hφ hCompact
  have hGI := integral_smooth_mul_neg_matrixGradient_divergence_symm
    (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun _ _ => contDiff_const)
    (fun _ i j => by simp only [Matrix.one_apply,eq_comm])
    (regularizedInverseNormPotential c0 t) φ hGamma hφ hCompact
  simp only [hOne,ContinuousLinearMap.id_apply] at hGI
  have hI := contDiff_neg_coordinateFluxDivergence_matrixGradient
    (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun _ _ => contDiff_const)
    (regularizedInverseNormPotential c0 t) hGamma
  simp only [hOne,ContinuousLinearMap.id_apply] at hI
  have hIntI : Integrable (fun z : R3 => φ z * (-coordinateFluxDivergence
      (gradient (regularizedInverseNormPotential c0 t)) z)) :=
    (hφ.continuous.mul hI.continuous).integrable_of_hasCompactSupport hCompact.mul_right
  have hIntR : Integrable (fun z : R3 => regularizedNormalCoefficientRemainder a c0 t p z * φ z) :=
    ((continuous_regularizedNormalCoefficientRemainder a ha c0 t ht p).mul hφ.continuous).integrable_of_hasCompactSupport hCompact.mul_left
  rw [hGA,hGI,← integral_add hIntI hIntR]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    unfold regularizedNormalCoefficientRemainder
    ring

theorem integral_inverseNormPotential_principal_of_normal_jets
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (p : P) (h0 : a (p,0) = 1) (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0)
    (hSym : ∀ z : R3, (a (p,z)).IsSymm)
    (φ : R3 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hCompact : HasCompactSupport φ) :
    (∫ z : R3, inverseNormPotential sphereSurfaceMass⁻¹ z *
      (-coordinateFluxDivergence (fun x => matrixOperatorMap (a (p,x)) (gradient φ x)) z)) =
      φ 0 + ∫ z : R3, normalCoefficientResidualProfile a sphereSurfaceMass⁻¹ (p,z) * φ z := by
  have haEntry (i j : Fin 3) : ContDiff ℝ ∞ (fun z : R3 => a (p,z) i j) :=
    ((normalResidualMatrixEntryL i j).contDiff.comp ha).comp (contDiff_const.prodMk contDiff_id)
  have hOne : matrixOperatorMap (1 : Matrix (Fin 3) (Fin 3) ℝ) = ContinuousLinearMap.id ℝ R3 := by
    change matrixOperatorAlgEquiv 1 = 1
    exact map_one matrixOperatorAlgEquiv
  let A : R3 → ℝ := fun z => -coordinateFluxDivergence
    (fun x => matrixOperatorMap (a (p,x)) (gradient φ x)) z
  let I : R3 → ℝ := fun z => -coordinateFluxDivergence (gradient φ) z
  have hAc : Continuous A := (contDiff_neg_coordinateFluxDivergence_matrixGradient
    (fun z => a (p,z)) haEntry φ hφ).continuous
  have hAs : HasCompactSupport A := hasCompactSupport_neg_coordinateFluxDivergence_matrixGradient
    (fun z => a (p,z)) φ hCompact
  have hIc := (contDiff_neg_coordinateFluxDivergence_matrixGradient
    (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun _ _ => contDiff_const) φ hφ).continuous
  have hIs := hasCompactSupport_neg_coordinateFluxDivergence_matrixGradient
    (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) φ hCompact
  simp only [hOne,ContinuousLinearMap.id_apply] at hIc hIs
  have hL := tendsto_integral_regularizedInverseNormPotential_mul_continuous_compact
    sphereSurfaceMass⁻¹ A hAc hAs
  have hR := (tendsto_integral_regularizedInverseNormPotential_mul_continuous_compact
    sphereSurfaceMass⁻¹ I hIc hIs).add
      (tendsto_integral_regularizedNormalCoefficientRemainder_mul_compact
        a ha p h0 h1 sphereSurfaceMass⁻¹ φ hφ.continuous hCompact)
  have hEq : (fun t : ℝ => ∫ z : R3, regularizedInverseNormPotential sphereSurfaceMass⁻¹ t z * A z) =ᶠ[𝓝[>] 0]
      (fun t => (∫ z : R3, regularizedInverseNormPotential sphereSurfaceMass⁻¹ t z * I z) +
        ∫ z : R3, regularizedNormalCoefficientRemainder a sphereSurfaceMass⁻¹ t p z * φ z) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact integral_regularizedInverseNormPotential_principal_split a ha p hSym sphereSurfaceMass⁻¹ t ht φ hφ hCompact
  have h := tendsto_nhds_unique hL (hR.congr' hEq.symm)
  change (∫ z : R3, inverseNormPotential sphereSurfaceMass⁻¹ z * A z) = _
  rw [h]
  rw [show (∫ z : R3, inverseNormPotential sphereSurfaceMass⁻¹ z * I z) = φ 0 from
    integral_inverseNormPotential_mul_neg_coordinateFluxDivergence_gradient φ (hφ.of_le (by simp)) hCompact]

theorem measurable_normalCoefficientResidualProfile
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (c0 : ℝ) (p : P) :
    Measurable (fun z : R3 => normalCoefficientResidualProfile a c0 (p,z)) := by
  have hU (i j k : Fin 3) : Measurable (fun z : R3 => normalResidualUEntry a i j k (p,z)) :=
    ((contDiff_normalResidualUEntry a ha i j k).continuous.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hT (i j k l : Fin 3) : Measurable (fun z : R3 => normalResidualTEntry a i j k l (p,z)) :=
    ((contDiff_normalResidualTEntry a ha i j k l).continuous.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hC (i : Fin 3) : Measurable (fun z : R3 => z i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hPair (i j : Fin 3) : Measurable (fun z : R3 => z i*z j/‖z‖^3) :=
    ((hC i).mul (hC j)).div (continuous_norm.measurable.pow_const 3)
  have hQuad (k l i j : Fin 3) : Measurable (fun z : R3 => z k*z l*z i*z j/‖z‖^5) :=
    ((((hC k).mul (hC l)).mul (hC i)).mul (hC j)).div (continuous_norm.measurable.pow_const 5)
  unfold normalCoefficientResidualProfile
  exact ((Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => (measurable_const.mul (hU i j k)).mul (hPair k j)).add
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ =>
      Finset.measurable_sum _ fun l _ => (measurable_const.mul (hT i i k l)).mul (hPair k l))).sub
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
        (measurable_const.mul (hT i j k l)).mul (hQuad k l i j))

theorem integrable_normalCoefficientResidualProfile_mul_compact
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (c0 : ℝ) (p : P) (φ : R3 → ℝ) (hφ : Continuous φ) (hCompact : HasCompactSupport φ) :
    Integrable (fun z : R3 => normalCoefficientResidualProfile a c0 (p,z) * φ z) := by
  let B : R3 → ℝ := fun z => normalCoefficientResidualAbsoluteCoefficient a (p,z)
  have hB : Continuous B := (continuous_normalCoefficientResidualAbsoluteCoefficient a ha).comp
    (continuous_const.prodMk continuous_id)
  have hWeight : Continuous (fun z => B z * |φ z|) := hB.mul hφ.abs
  have hWeightCompact : HasCompactSupport (fun z => B z * |φ z|) := hCompact.abs.mul_left
  have hMajorant : Integrable (fun z : R3 => inverseNormPotential |c0| z * (B z * |φ z|)) :=
    integrable_inverseNormPotential_mul_continuous_compact |c0| _ hWeight hWeightCompact
  apply hMajorant.mono' ((measurable_normalCoefficientResidualProfile a ha c0 p).mul hφ.measurable).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : R3)] with z hz
  have hBound := abs_regularizedNormalCoefficientResidualProfile_le a c0 0 le_rfl p z hz
  rw [regularizedNormalCoefficientResidualProfile_zero] at hBound
  change ‖normalCoefficientResidualProfile a c0 (p,z) * φ z‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right hBound (abs_nonneg (φ z))).trans_eq
    (by dsimp only [inverseNormPotential,B];ring)

end OAI.AnisotropicCalderon.ConnectionError
