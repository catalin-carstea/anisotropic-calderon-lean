import Calderon.MixedKernelConstruction.MixedKernelConformalProductCriterion
import Calderon.NormalizedPrincipalMetricSmooth
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open MetricOperator ConnectionError ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
open scoped ContDiff InnerProductSpace

/-- The literal normalized principal matrix has the actual conformal covariant inverse. -/
theorem normalizedPrincipalMatrix_inv_eq
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (normalizedPrincipalMatrix A B)⁻¹ = (Matrix.trace (A*B⁻¹)/3) • B := by
  let c : ℝ := 3/Matrix.trace (A*B⁻¹)
  have hc : c ≠ 0 := (div_pos (by norm_num) (normalizedPrincipal_denominator_pos A B hA hB)).ne'
  letI : Invertible c := invertibleOfNonzero hc
  have hh : (c • B⁻¹)⁻¹ = c⁻¹ • (B⁻¹)⁻¹ := by
    simpa only [invOf_eq_inv] using Matrix.inv_smul B⁻¹ c
      ((Matrix.isUnit_iff_isUnit_det B⁻¹).mp hB.inv.isUnit)
  change (c • B⁻¹)⁻¹ = _
  rw [hh,Matrix.nonsing_inv_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit)]
  congr 1
  simp only [c,inv_div]

/-- Native specialization retains EXACT trace normalization and original second metric. -/
theorem referenceNormalizedPrincipalMatrix_inv_eq
    (S : KnownSideSourceData) (L lam : ℝ) (u : R3) :
    (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam u)⁻¹ =
      (referenceNormalizationTraceFamily S.g1 S.g2 L (lam,u)/3) • dilatedMetric S.g2 lam u := by
  exact normalizedPrincipalMatrix_inv_eq _ _
    (EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef S.g1 S.g1_admissible lam) u)
    (dilatedMetric_posDef S.g2 S.g2_admissible lam u)

/-- The original native geometric test equals the reference/normalized metric test, with actual conformal factors. -/
theorem productHessianStrictAt_reference_normalized_iff
    (S : KnownSideSourceData) (L lam : ℝ) (x y : R3) (rho : R3 × R3 → ℝ) :
    ProductHessianStrictAt (referenceMetric (dilatedMetric S.g1 lam) L)
      (fun u => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam u)⁻¹) x y rho ↔
    ProductHessianStrictAt (dilatedMetric S.g1 lam) (dilatedMetric S.g2 lam) x y rho := by
  let c1 : R3 → ℝ := fun u => Real.exp (-2*L*referenceCoordinateDepth u)
  let c2 : R3 → ℝ := fun u => referenceNormalizationTraceFamily S.g1 S.g2 L (lam,u)/3
  have hFirst : referenceMetric (dilatedMetric S.g1 lam) L =
      fun u => c1 u • dilatedMetric S.g1 lam u := by
    funext u
    change Real.exp (2*(-L*referenceCoordinateDepth u)) • dilatedMetric S.g1 lam u = _
    have hh : 2*(-L*referenceCoordinateDepth u) = -2*L*referenceCoordinateDepth u := by ring
    rw [hh]
  have hSecond : (fun u => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam u)⁻¹) =
      fun u => c2 u • dilatedMetric S.g2 lam u := by
    funext u
    exact referenceNormalizedPrincipalMatrix_inv_eq S L lam u
  have hg1 : ContDiff ℝ ∞ (metricOperatorField (dilatedMetric S.g1 lam)) :=
    (contDiff_metricOperatorField S.g1 S.g1_admissible).comp (contDiff_id.const_smul lam)
  have hg2 : ContDiff ℝ ∞ (metricOperatorField (dilatedMetric S.g2 lam)) :=
    (contDiff_metricOperatorField S.g2 S.g2_admissible).comp (contDiff_id.const_smul lam)
  have hc1 : ContDiff ℝ ∞ c1 := (contDiff_const.mul contDiff_referenceCoordinateDepth).exp
  have hc2 : ContDiff ℝ ∞ c2 :=
    ((contDiff_referenceNormalizationTraceFamily S.g1 S.g2 S.g1_admissible S.g2_admissible L).comp
      (contDiff_const.prodMk contDiff_id)).div_const 3
  rw [hFirst,hSecond]
  exact productHessianStrictAt_smul _ _ c1 c2 x y rho
    (hg1.differentiable (by simp) x) (dilatedMetric_posDef S.g1 S.g1_admissible lam x)
    (hg2.differentiable (by simp) y) (dilatedMetric_posDef S.g2 S.g2_admissible lam y)
    (hc1.differentiable (by simp) x) (hc2.differentiable (by simp) y)
    (Real.exp_pos _) (div_pos (referenceNormalizationTraceFamily_pos S.g1 S.g2
      S.g1_admissible S.g2_admissible L (lam,y)) (by norm_num))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
