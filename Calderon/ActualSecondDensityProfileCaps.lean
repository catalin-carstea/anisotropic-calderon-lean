import Calderon.ActualSecondGeometryCaps
import Calderon.ActualSScalarCoefficientBounds
import Calderon.ActualOriginalSDirectPhysicalFormBounds

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSecondDensityProfileCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualHigherSFormation ActualHigherSSecondAdjoint
  ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift ActualHorizontalNormBridge
  ActualSecondGeometryCaps ActualSScalarCoefficientBounds ReferenceWeightedApproximation

private lemma abs_add_le'' (x y : ℝ) : |x+y| ≤ |x|+|y| := by
  simpa only [Real.norm_eq_abs] using norm_add_le x y

private lemma square_mul_fderiv (r Q : R3 → ℝ) (x v : R3)
    (hr : HasFDerivAt r (fderiv ℝ r x) x) (hQ : HasFDerivAt Q (fderiv ℝ Q x) x) :
    fderiv ℝ (fun y => (r y)^2 * Q y) x v =
      (r x)^2 * (fderiv ℝ Q x v) + 2 * r x * Q x * (fderiv ℝ r x v) := by
  change (fderiv ℝ ((fun y => (r y)^2) * Q) x) v = _
  rw [((hr.pow 2).mul hQ).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

attribute [local irreducible] referenceRadius referenceDensityPrincipalFrameCoefficient
  referenceMetricGramFrame

/-- The derivative direction k is independent of the original two Q indices. -/
theorem secondCoefficient_frame_fderiv_any (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (i j k : Fin 3) (x : R3) :
    fderiv ℝ (secondCoefficient g g2 L q dr Ar p i j) x
        (referenceMetricGramFrame g L (q,x) k) =
      (referenceRadius dr Ar p L x)^2 *
        (fderiv ℝ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
            (referenceMetricGramFrame g L (q,x) k) +
          2 * referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
            referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x k) := by
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hQ : ContDiff ℝ ∞ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
      (contDiff_const.prodMk contDiff_id)
  have hRf0 := referenceRadius_mul_horizontalLogDerivative_eq_fderiv g L q
    (referenceRadius dr Ar p L) hR x (referenceRadius_pos dr Ar p L x hdr hAr).ne' k
  have hRf : fderiv ℝ (referenceRadius dr Ar p L) x (referenceMetricGramFrame g L (q,x) k) =
      referenceRadius dr Ar p L x *
        referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x k := by
    have hx := congrArg (fderiv ℝ (referenceRadius dr Ar p L) x)
      (ActualHigherSZeroCoefficientBounds.conformalFrame_coordinateVector_eq g L q x k)
    exact hx.symm.trans hRf0.symm
  change fderiv ℝ (fun y => (referenceRadius dr Ar p L y)^2 *
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
      (referenceMetricGramFrame g L (q,x) k) = _
  have hd := square_mul_fderiv (referenceRadius dr Ar p L)
    (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
    (referenceMetricGramFrame g L (q,x) k)
    (hR.differentiable (by simp) x).hasFDerivAt (hQ.differentiable (by simp) x).hasFDerivAt
  calc _ = _ := hd
       _ = _ := by rw [hRf]; ring

/-- Complete density product rule, with no diagonal restriction or Q symmetry. -/
theorem densityDerivativeCoefficient_second_eq_any (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (i j k : Fin 3) (x : R3) :
    densityDerivativeCoefficient g L q k (secondCoefficient g g2 L q dr Ar p i j) x =
      (referenceRadius dr Ar p L x)^2 *
        (referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
            referenceWeightedFrameDivergence g L q k x +
          referenceDensityFamily g L (q,x) *
            (fderiv ℝ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
                (referenceMetricGramFrame g L (q,x) k) +
              2 * referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
                referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x k)) := by
  unfold densityDerivativeCoefficient
  rw [secondCoefficient_frame_fderiv_any g g2 hg hg2 L q dr Ar p hdr hAr i j k x]
  unfold secondCoefficient
  ring

/-- A genuine pre-profile cap on every original density derivative of r²Q. Fixed g2. -/
theorem exists_second_density_uniform_profile_bound (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ dr Ar : ℝ, ∀ p : ℕ, 0 < dr → dr ≤ 1 → 0 < Ar → 1 ≤ p →
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      1 ≤ actualReferenceBeta g L q dr Ar p x → ∀ i j k : Fin 3,
      |densityDerivativeCoefficient g L q k (secondCoefficient g g2 L q dr Ar p i j) x| ≤
        Cd*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x := by
  obtain ⟨A,hA,hGeom⟩ := exists_geometryCaps g g2 hg hg2 L K hK
  obtain ⟨Cf,hCf,hLog⟩ := exists_profile_horizontal_log_derivative_bound g hg L hL K hK
  obtain ⟨CQ1,hCQ1,hDQ⟩ := exists_principal_horizontal_derivative_bound g g2 hg hg2 L K hK
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  let Cd : ℝ := A^2+A*CQ1+2*A^2*Cf
  have hCd : 0 ≤ Cd := by dsimp [Cd]; positivity
  refine ⟨Cd,hCd,?_⟩
  intro dr Ar p hdr hdr1 hAr hp q hq x hx hb i j k
  have gc := hGeom q hq x hx
  let R2 := (referenceRadius dr Ar p L x)^2
  let beta := actualReferenceBeta g L q dr Ar p x
  let mu := referenceDensityFamily g L (q,x)
  let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x i j
  let dv := referenceWeightedFrameDivergence g L q k x
  let dQ := fderiv ℝ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
    (referenceMetricGramFrame g L (q,x) k)
  let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x k
  have hR20 : 0 ≤ R2 := sq_nonneg _
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have h1 : |Q*dv| ≤ A*A := by
    rw [abs_mul]
    exact mul_le_mul (gc.principal i j) (gc.weighted_divergence k) (abs_nonneg _) hA0
  have hf : |f| ≤ Cf*beta := hLog dr Ar p hdr hdr1 hAr hp q hq x hx hb k
  have hdQ : |dQ| ≤ CQ1 := hDQ q hq x hx k i j
  have h2 : |dQ+2*Q*f| ≤ CQ1+2*A*(Cf*beta) := by
    refine (abs_add_le'' _ _).trans (add_le_add hdQ ?_)
    rw [abs_mul,abs_mul,abs_two]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (gc.principal i j) (by norm_num)) hf
      (abs_nonneg _) (by positivity)
  have h3 : |Q*dv+mu*(dQ+2*Q*f)| ≤ A*A+A*(CQ1+2*A*(Cf*beta)) := by
    refine (abs_add_le'' _ _).trans (add_le_add h1 ?_)
    rw [abs_mul]
    exact mul_le_mul gc.density h2 (abs_nonneg _) hA0
  have hScale : A*A+A*(CQ1+2*A*(Cf*beta)) ≤ Cd*beta := by
    have hExtra : 0 ≤ (A^2+A*CQ1)*(beta-1) := mul_nonneg
      (add_nonneg (sq_nonneg A) (mul_nonneg hA0 hCQ1)) (sub_nonneg.mpr hb)
    dsimp only [Cd]
    nlinarith only [hExtra]
  rw [densityDerivativeCoefficient_second_eq_any g g2 hg hg2 L q dr Ar p hdr hAr i j k x]
  change |R2*(Q*dv+mu*(dQ+2*Q*f))| ≤ Cd*R2*beta
  rw [abs_mul,abs_of_nonneg hR20]
  calc
    _ ≤ R2*(A*A+A*(CQ1+2*A*(Cf*beta))) := mul_le_mul_of_nonneg_left h3 hR20
    _ ≤ R2*(Cd*beta) := mul_le_mul_of_nonneg_left hScale hR20
    _ = Cd*R2*beta := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSecondDensityProfileCaps
