import Calderon.WeightedRaisingBounds
import Calderon.HessianContraction

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.ProfileHessianEnergy
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial SphereHarmonic
  WeightedFischerSquare SmoothMetricFrame FischerConnectionTransport
  IntegratedFischerIdentities FiniteRaisingEnergy WeightedRaisingBounds
  MetricFrameTrace ReferenceDensityBounds HessianContraction FischerDensityIntegration
  FiniteCovariantCurvature FrameCurvaturePolynomial MovingFrameConnection

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric finitePolynomialField
variable {ι : Type*} [Fintype ι]

def referenceProfileMass (g : MatrixField) (lam δ R L : ℝ) (p : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*referenceProfileNorm g lam δ R p L x*
    fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)

def referenceProfileTraceHessianEnergy (g : MatrixField) (lam δ R L : ℝ) (p : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k : ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*(2*k*∑ i : Fin 3,
    referenceFrameHessianCoefficient g L lam (referenceLogRadius δ R p L) x i i)*
    fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)

lemma integrable_referenceProfileTraceHessianEnergy (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) :
    Integrable (fun x : R3 => referenceDensityFamily g L (lam,x)*(2*k*∑ i : Fin 3,
      referenceFrameHessianCoefficient g L lam (referenceLogRadius δ R p L) x i i)*
      fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
  have hH : ContDiff ℝ ∞ (fun x : R3 => 2*k*∑ i : Fin 3,
      referenceFrameHessianCoefficient g L lam (referenceLogRadius δ R p L) x i i) :=
    contDiff_const.mul (ContDiff.sum (fun i _ =>
      contDiff_referenceFrameHessianCoefficient g hg L lam _
        (contDiff_log_referenceRadius δ R p L hδ hR) i i))
  exact integrable_referenceDensity_weighted_fischerPair g hg L lam _ hH.continuous b b c c hc hc hcompact

lemma referenceProfile_loweredHessian_eq_contraction (g : MatrixField)
    (lam δ R L : ℝ) (p k : ℕ) (v : MvPolynomial (Fin 3) ℝ) (x : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      (2*(k:ℝ)*referenceFrameHessianCoefficient g L lam (referenceLogRadius δ R p L) x i j)*
        fischerInner (pderiv i v) (pderiv j v)) =
      referenceProfileHessianContraction g lam δ R p L x (referenceMetricGramFrame g L (lam,x)) k v := by
  simp only [referenceProfileHessianContraction,referenceProfileHessianBilinear,
    MetricVolume.coordinateHessianBilinear_apply,referenceFrameHessianCoefficient,
    referenceConnectionFamily,AngularPolynomial.inverseMetricOperator,Finset.mul_sum,mul_assoc]

lemma referenceProfileMass_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) :
    0 ≤ referenceProfileMass g lam δ R L p b c := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le
    (Real.sqrt_nonneg _)) (fischerInner_self_nonneg _)

lemma referenceProfile_loweredHessian_pointwise_le (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (L c0 nu J1 J2 D : ℝ) (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p : ℕ) (hp : 1 ≤ p) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0) (x : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      (2*(k:ℝ)*referenceFrameHessianCoefficient g L lam (referenceLogRadius δ R p L) x i j)*
        fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x))) ≤
      -2*nu*(k:ℝ)^2*referenceProfileNorm g lam δ R p L x*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) := by
  by_cases hx : x ∈ K
  · rw [referenceProfile_loweredHessian_eq_contraction]
    exact referenceProfileHessianContraction_le g K L c0 nu J1 J2 D hbounds lam hlam δ hδ hδ1 R hR p hp x hx _
      (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)) k _
      (finitePolynomialField_harmonicHomogeneous k b hb c x).1
  · simp only [hzero x hx,map_zero,fischerInner_zero_left,mul_zero,Finset.sum_const_zero,le_refl]

lemma referenceProfile_loweredHessianEnergy_le (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (L c0 nu J1 J2 D : ℝ) (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p : ℕ) (hp : 1 ≤ p) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0) :
    referenceLoweredHessianEnergy g L lam b c (referenceLogRadius δ R p L) k ≤
      (-2*nu*(k:ℝ)^2)*referenceProfileMass g lam δ R L p b c := by
  have hH := integrable_referenceLoweredHessian g hg L lam b c _ (k:ℝ) hc
    (contDiff_log_referenceRadius δ R p L hδ hR) hcompact
  have hM := integrable_referenceProfileNorm_fischerSquare g hg lam δ R L p hδ hR b c hc hcompact
  calc
    _ ≤ ∫ x : R3, (-2*nu*(k:ℝ)^2)*(referenceDensityFamily g L (lam,x)*referenceProfileNorm g lam δ R p L x*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
      apply integral_mono hH (hM.const_mul _)
      intro x
      have hh := mul_le_mul_of_nonneg_left
        (referenceProfile_loweredHessian_pointwise_le g hg K L c0 nu J1 J2 D hbounds lam hlam δ hδ hδ1 R hR p hp k b hb c hzero x)
        (referenceDensityFamily_pos g hg L (lam,x)).le
      calc
        _ ≤ referenceDensityFamily g L (lam,x)*(-2*nu*(k:ℝ)^2*referenceProfileNorm g lam δ R p L x*
            fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := hh
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

lemma referenceProfileTraceHessian_pointwise_le (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (L c0 nu J1 J2 D : ℝ) (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p : ℕ) (hp : 1 ≤ p) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0) (x : R3) :
    (2*(k:ℝ)*∑ i : Fin 3, referenceFrameHessianCoefficient g L lam (referenceLogRadius δ R p L) x i i)*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) ≤
      -6*nu*(k:ℝ)*referenceProfileNorm g lam δ R p L x*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) := by
  by_cases hx : x ∈ K
  · have he := referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)
    have hdiag (i : Fin 3) : referenceFrameHessianCoefficient g L lam (referenceLogRadius δ R p L) x i i ≤
        -nu*referenceProfileNorm g lam δ R p L x := by
      have h := (hbounds.1 lam hlam δ hδ hδ1 R hR p hp x hx).2.1 (referenceMetricGramFrame g L (lam,x) i)
      rw [IsMetricOrthonormalFrame_unit _ _ he i,mul_one] at h
      simpa only [referenceFrameHessianCoefficient,referenceConnectionFamily] using h
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hdiag i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*(k:ℝ) by positivity)
    have hm' := mul_le_mul_of_nonneg_right hm (fischerInner_self_nonneg (finitePolynomialField b c x))
    convert hm' using 1 <;> ring
  · simp only [hzero x hx,fischerInner_zero_left,mul_zero,le_refl]

lemma referenceProfileTraceHessianEnergy_le (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (L c0 nu J1 J2 D : ℝ) (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p : ℕ) (hp : 1 ≤ p) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0) :
    referenceProfileTraceHessianEnergy g lam δ R L p b c k ≤
      (-6*nu*(k:ℝ))*referenceProfileMass g lam δ R L p b c := by
  have hJ := integrable_referenceProfileTraceHessianEnergy g hg lam δ R L p hδ hR b c k hc hcompact
  have hM := integrable_referenceProfileNorm_fischerSquare g hg lam δ R L p hδ hR b c hc hcompact
  calc
    _ ≤ ∫ x : R3, (-6*nu*(k:ℝ))*(referenceDensityFamily g L (lam,x)*referenceProfileNorm g lam δ R p L x*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
      apply integral_mono hJ (hM.const_mul _)
      intro x
      convert mul_le_mul_of_nonneg_left
        (referenceProfileTraceHessian_pointwise_le g hg K L c0 nu J1 J2 D hbounds lam hlam δ hδ hδ1 R hR p hp k b c hzero x)
        (referenceDensityFamily_pos g hg L (lam,x)).le using 1 <;> ring
    _ = _ := integral_const_mul _ _

lemma referenceProfileFrameEnergy_square_difference (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p k : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k (-1) x) =
      (∫ x : R3, referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k 1 x) +
      referenceProfileTraceHessianEnergy g lam δ R L p b c k :=
  compact_referenceLogRadius_weightedFrameEnergy_square_difference g hg L lam δ R p k hδ hR b c hc hcompact

lemma referenceCovariantPolynomialDerivative_eq_zero_off_closed (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (K : Set R3) (hK : IsClosed K)
    (hU : ∀ y ∉ K, finitePolynomialField b c y = 0) (x V : R3) (hx : x ∉ K) :
    referenceCovariantPolynomialDerivative g L lam b c x V = 0 := by
  let F : R3 × R3 → ℝ := evaluatedReferencePolynomialField g L lam b c
  apply referenceMovingFramePolynomial_injective g hg L lam x
  intro v
  have hO : IsOpen {z : R3 × R3 | z.1 ∉ K} := hK.isOpen_compl.preimage continuous_fst
  have he : F =ᶠ[𝓝 (x,v)] (fun _ : R3 × R3 => (0:ℝ)) := by
    filter_upwards [hO.mem_nhds hx] with z hz
    change evaluatedReferencePolynomialField g L lam b c z = 0
    rw [evaluatedReferencePolynomialField_eq,hU z.1 hz]
    simp [referenceMovingFramePolynomial,movingFramePolynomial]
  have hD : fderiv ℝ F (x,v) = 0 := by
    simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜 := ℝ)
  have hH := fderiv_evaluatedReferencePolynomialField_horizontal g hg L lam b c hc x v V
  change fderiv ℝ F (x,v) (V,-referenceConnectionFamily g L (lam,x) V v) = _ at hH
  rw [hD] at hH
  simpa [referenceMovingFramePolynomial,movingFramePolynomial] using hH.symm

lemma referenceWeightedPolynomialDerivative_eq_zero_off_closed (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (K : Set R3) (hK : IsClosed K)
    (hU : ∀ y ∉ K, finitePolynomialField b c y = 0) (x V : R3) (hx : x ∉ K)
    (f : R3 → ℝ) (k s : ℝ) :
    referenceWeightedPolynomialDerivative g L lam b c f k s x V = 0 := by
  simp only [referenceWeightedPolynomialDerivative,
    referenceCovariantPolynomialDerivative_eq_zero_off_closed g hg L lam b c hc K hK hU x V hx,
    hU x hx,mul_zero,add_zero]

lemma referenceWeightedFrameEnergy_eq_zero_off_closed (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (K : Set R3) (hK : IsClosed K)
    (hU : ∀ y ∉ K, finitePolynomialField b c y = 0) (x : R3) (hx : x ∉ K)
    (f : R3 → ℝ) (k s : ℝ) : referenceWeightedFrameEnergy g L lam b c f k s x = 0 := by
  simp only [referenceWeightedFrameEnergy,
    referenceWeightedPolynomialDerivative_eq_zero_off_closed g hg L lam b c hc K hK hU x _ hx,
    fischerInner_zero_left,Finset.sum_const_zero]

lemma referenceLoweredWeightedTraceField_eq_zero_off_closed (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (K : Set R3) (hK : IsClosed K)
    (hU : ∀ y ∉ K, finitePolynomialField b c y = 0) (x : R3) (hx : x ∉ K)
    (f : R3 → ℝ) (k s : ℝ) : referenceLoweredWeightedTraceField g L lam b c f k s x = 0 := by
  rw [← polynomialDivergence_referenceWeightedFramePolynomialField]
  simp only [polynomialDivergence,referenceWeightedFramePolynomialField,
    referenceWeightedPolynomialDerivative_eq_zero_off_closed g hg L lam b c hc K hK hU x _ hx,
    map_zero,Finset.sum_const_zero]

end OAI.AnisotropicCalderon.ProfileHessianEnergy
