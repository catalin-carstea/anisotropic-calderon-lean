import Calderon.FiniteRaisingEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.WeightedRaisingBounds
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial SphereHarmonic
  WeightedFischerSquare SmoothMetricFrame FischerConnectionTransport
  IntegratedFischerIdentities FiniteRaisingEnergy PolynomialSlotCompatibility
  MetricFrameTrace ReferenceDensityBounds FischerDensityIntegration

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric finitePolynomialField
  referenceCovariantPolynomialDerivative
variable {ι : Type*} [Fintype ι]

lemma referenceWeightedFramePolynomialField_plus_eq (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k : ℕ) (x : R3) :
    referenceWeightedFramePolynomialField g L lam b c f k 1 x =
      weightedDerivativePlus k (fun i => fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i))
        (finitePolynomialField b c x) (fun i => referenceCovariantPolynomialDerivative g L lam b c x
          (referenceMetricGramFrame g L (lam,x) i)) := by
  funext i
  simp only [referenceWeightedFramePolynomialField,referenceWeightedPolynomialDerivative,
    weightedDerivativePlus,map_mul,map_one,one_mul,mul_assoc]

lemma referenceWeightedFramePolynomialField_minus_eq (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k : ℕ) (x : R3) :
    referenceWeightedFramePolynomialField g L lam b c f k (-1) x =
      weightedDerivativeMinus k (fun i => fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i))
        (finitePolynomialField b c x) (fun i => referenceCovariantPolynomialDerivative g L lam b c x
          (referenceMetricGramFrame g L (lam,x) i)) := by
  funext i
  simp only [referenceWeightedFramePolynomialField,referenceWeightedPolynomialDerivative,
    weightedDerivativeMinus,map_mul,map_neg,map_one,neg_one_mul,mul_assoc]

lemma referenceLoweredWeightedTraceField_pointwise_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (s : ℝ) (x : R3) :
    fischerInner (referenceLoweredWeightedTraceField g L lam b c f k s x)
      (referenceLoweredWeightedTraceField g L lam b c f k s x) ≤
      ((k:ℝ)+2)*referenceWeightedFrameEnergy g L lam b c f k s x := by
  have hq : ∀ i : Fin 3, (referenceWeightedFramePolynomialField g L lam b c f k s x i).IsHomogeneous k :=
    fun i => (referenceWeightedPolynomialDerivative_harmonicHomogeneous g hg L lam k hk b hb c f s x
      (referenceMetricGramFrame g L (lam,x) i)).1
  have h := fischerInner_divergence_self_le hk _ hq
  rw [polynomialDivergence_referenceWeightedFramePolynomialField] at h
  simpa only [Fintype.card_fin,referenceWeightedFramePolynomialField,referenceWeightedFrameEnergy,
    Nat.cast_ofNat,show (k:ℝ)+(3:ℝ)-1=(k:ℝ)+2 by ring] using h

lemma metricDifferentialNorm_sq_eq_frame_sum (g : MatrixField)
    (hp : ∀ x, (g x).PosDef) (f : R3 → ℝ) (x : R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame (metricOperatorField g x) e) :
    metricDifferentialNorm g f x ^ 2 = ∑ i : Fin 3, (fderiv ℝ f x (e i))^2 := by
  have hq : coefficientQuadratic (inverseMetricOperator g) x (gradient f x) =
      ∑ i : Fin 3, (fderiv ℝ f x (e i))^2 := by
    unfold coefficientQuadratic
    rw [inverseMetricOperator_eq_matrix_inverse_of_posDef g hp,
      inverseMatrix_metricFrame_sum (g x) (hp x) e (by simpa only [metricOperatorField] using he)]
    simp only [sum_inner,real_inner_smul_left]
    apply Finset.sum_congr rfl
    intro i hi
    simp [inner_gradient_left,inner_gradient_right,pow_two]
  unfold metricDifferentialNorm
  rw [hq,Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]

lemma referenceMetricDifferentialNorm_sq_eq_frame_sum (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (x : R3) :
    metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x ^2 =
      ∑ i : Fin 3, (fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i))^2 :=
  metricDifferentialNorm_sq_eq_frame_sum _ (dilatedReferenceMetric_posDef g hg lam L) f x _
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x))

lemma referenceLoweredWeightedTraceField_mixed_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (x : R3) :
    fischerInner (referenceLoweredWeightedTraceField g L lam b c f k 1 x)
      (referenceLoweredWeightedTraceField g L lam b c f k 1 x) ≤
      2*fischerInner (referenceLoweredWeightedTraceField g L lam b c f k (-1) x)
        (referenceLoweredWeightedTraceField g L lam b c f k (-1) x) +
      8*(k:ℝ)^3*metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x ^2*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) := by
  have hv : (finitePolynomialField b c x).IsHomogeneous k :=
    (finitePolynomialField_harmonicHomogeneous k b hb c x).1
  have h := fischerInner_weightedDerivative_divergence_bound
    (fun i => fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i)) (finitePolynomialField b c x)
    (fun i => referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i))
    hv (metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x)
    (referenceMetricDifferentialNorm_sq_eq_frame_sum g hg L lam f x).symm.le
  rw [← referenceWeightedFramePolynomialField_plus_eq,← referenceWeightedFramePolynomialField_minus_eq,
    polynomialDivergence_referenceWeightedFramePolynomialField,
    polynomialDivergence_referenceWeightedFramePolynomialField] at h
  exact h

lemma referenceLoweredWeightedTraceField_convex_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (x : R3) (zeta : ℝ)
    (hz : 0 ≤ zeta) (hz1 : zeta ≤ 1) :
    fischerInner (referenceLoweredWeightedTraceField g L lam b c f k 1 x)
      (referenceLoweredWeightedTraceField g L lam b c f k 1 x) ≤
      (1-zeta)*(((k:ℝ)+2)*referenceWeightedFrameEnergy g L lam b c f k 1 x) +
      zeta*(2*fischerInner (referenceLoweredWeightedTraceField g L lam b c f k (-1) x)
        (referenceLoweredWeightedTraceField g L lam b c f k (-1) x) +
        8*(k:ℝ)^3*metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x ^2*
          fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
  have h1 := mul_le_mul_of_nonneg_left
    (referenceLoweredWeightedTraceField_pointwise_bound g hg L lam k hk b hb c f 1 x)
    (sub_nonneg.mpr hz1)
  have h2 := mul_le_mul_of_nonneg_left
    (referenceLoweredWeightedTraceField_mixed_bound g hg L lam k hk b hb c f x) hz
  nlinarith

lemma fderiv_referenceLogRadius_ne_zero (δ R L : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p) (x : R3) :
    fderiv ℝ (referenceLogRadius δ R p L) x ≠ 0 := by
  have hpp : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have ha : (p:ℝ)*logSlope δ (referenceDepth L x) ≠ 0 :=
    (mul_pos hpp (logSlope_pos δ _ hδ)).ne'
  have ht := fderiv_referenceDepth_ne_zero L hL.ne' x
  change fderiv ℝ (fun y => Real.log (referenceRadius δ R p L y)) x ≠ 0
  rw [log_referenceRadius δ R p L hδ hR,fderiv_logProfile δ (Real.log R) p (referenceDepth L) x hδ
    ((contDiff_referenceDepth L).differentiable (by simp) x)]
  unfold profileDifferential
  exact smul_ne_zero ha ht

lemma referenceProfileNorm_pos (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L)
    (hp : 1 ≤ p) (x : R3) : 0 < referenceProfileNorm g lam δ R p L x :=
  metricDifferentialNorm_pos _ (dilatedReferenceMetric_posDef g hg lam L) _ x
    (fderiv_referenceLogRadius_ne_zero δ R L p hδ hR hL hp x)

lemma continuous_referenceProfileNorm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Continuous (referenceProfileNorm g lam δ R p L) :=
  continuous_metricDifferentialNorm _ (dilatedReferenceMetric_smooth_entries g hg lam L)
    (dilatedReferenceMetric_posDef g hg lam L) _ (contDiff_log_referenceRadius δ R p L hδ hR)

lemma continuous_referenceProfileNorm_inv (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p) :
    Continuous (fun x => (referenceProfileNorm g lam δ R p L x)⁻¹) :=
  (continuous_referenceProfileNorm g hg lam δ R L p hδ hR).inv₀
    (fun x => (referenceProfileNorm_pos g hg lam δ R L p hδ hR hL hp x).ne')

lemma referenceProfileTrace_convex_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (profileP k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (x : R3) (c1 : ℝ) (hc1 : 0 ≤ c1)
    (hbeta : 0 < referenceProfileNorm g lam δ R profileP L x)
    (hc1beta : c1 ≤ referenceProfileNorm g lam δ R profileP L x) :
    fischerInner (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R profileP L) k 1 x)
      (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R profileP L) k 1 x) ≤
      (1-c1/referenceProfileNorm g lam δ R profileP L x)*(((k:ℝ)+2)*referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R profileP L) k 1 x) +
      (c1/referenceProfileNorm g lam δ R profileP L x)*(2*fischerInner
        (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R profileP L) k (-1) x)
        (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R profileP L) k (-1) x) +
        8*(k:ℝ)^3*referenceProfileNorm g lam δ R profileP L x ^2*
          fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) :=
  referenceLoweredWeightedTraceField_convex_bound g hg L lam k hk b hb c _ x _
    (div_nonneg hc1 hbeta.le) ((div_le_one hbeta).mpr hc1beta)

variable {κ : Type*} [Fintype κ]

lemma integrable_referenceDensity_weighted_fischerPair (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a : R3 → ℝ) (ha : Continuous a)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) : Integrable (fun x => referenceDensityFamily g L (lam,x)*a x*
      fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  have hr : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  exact ((hr.continuous.mul ha).mul (contDiff_fischerPair b d c z hc hz).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_fischerPair b d c z hcompact).mul_left

lemma integrable_referenceDensity_weighted_frameEnergy (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a : R3 → ℝ) (ha : Continuous a)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*a x*referenceWeightedFrameEnergy g L lam b c f k s x) := by
  have hr : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  exact integrable_referenceWeightedFrameEnergy g hg L lam _ (hr.continuous.mul ha) b c f k s hc hf hcompact

lemma integrable_referenceDensity_weighted_traceSquare (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a : R3 → ℝ) (ha : Continuous a)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*a x*fischerInner
      (referenceLoweredWeightedTraceField g L lam b c f k s x)
      (referenceLoweredWeightedTraceField g L lam b c f k s x)) := by
  simp_rw [referenceLoweredWeightedTraceField_eq_finite]
  exact integrable_referenceDensity_weighted_fischerPair g hg L lam a ha _ _ _ _
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f k s hc hf)
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f k s hc hf)
    (hasCompactSupport_referenceLoweredWeightedTensorCoefficientFamily g L lam c f k s hcompact)

lemma integrable_referenceProfileNorm_fischerSquare (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) : Integrable (fun x =>
      referenceDensityFamily g L (lam,x)*referenceProfileNorm g lam δ R p L x*
      fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) :=
  integrable_referenceDensity_weighted_fischerPair g hg L lam _
    (continuous_referenceProfileNorm g hg lam δ R L p hδ hR) b b c c hc hc hcompact

lemma integrable_referenceProfileNorm_inv_frameEnergy (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) : Integrable (fun x =>
      referenceDensityFamily g L (lam,x)*(referenceProfileNorm g lam δ R p L x)⁻¹*
      referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k s x) :=
  integrable_referenceDensity_weighted_frameEnergy g hg L lam _
    (continuous_referenceProfileNorm_inv g hg lam δ R L p hδ hR hL hp) b c _ k s hc
    (contDiff_log_referenceRadius δ R p L hδ hR) hcompact

lemma integrable_referenceProfileNorm_inv_traceSquare (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) : Integrable (fun x =>
      referenceDensityFamily g L (lam,x)*(referenceProfileNorm g lam δ R p L x)⁻¹*fischerInner
      (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k s x)
      (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k s x)) :=
  integrable_referenceDensity_weighted_traceSquare g hg L lam _
    (continuous_referenceProfileNorm_inv g hg lam δ R L p hδ hR hL hp) b c _ k s hc
    (contDiff_log_referenceRadius δ R p L hδ hR) hcompact

end OAI.AnisotropicCalderon.WeightedRaisingBounds
