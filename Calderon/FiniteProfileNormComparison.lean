import Calderon.FiniteProfileRaisingGain
import Calderon.MetricFiberCovectorTransport

set_option autoImplicit false
set_option maxSynthPendingDepth 10
universe u
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.FiniteProfileNormComparison
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial SphereHarmonic
  WeightedFischerSquare SmoothMetricFrame FischerConnectionTransport
  IntegratedFischerIdentities FiniteRaisingEnergy WeightedRaisingBounds
  ProfileHessianEnergy IntegratedProfileConvexity ReferenceDensityBounds
  FiniteProfileRaisingGain MetricFiberMeasure MetricFiberFischer MetricFiberCovectorTransport
  FrameCurvaturePolynomial
attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric finitePolynomialField
variable {ι : Type*} [Fintype ι]

def referenceProfileSecondMass (g : MatrixField) (lam δ R L : ℝ) (p : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*referenceProfileNorm g lam δ R p L x^2*
    fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)

def referenceProfileModeFischerEnergy (g : MatrixField) (lam δ R L : ℝ) (p k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) : ℝ :=
  referenceProfileFrameEnergy g lam δ R L p b c 0 1 +
    (1+(k:ℝ))^2*referenceProfileSecondMass g lam δ R L p b c +
    (1+(k:ℝ))*referenceProfileWeightedFrameEnergy g lam δ R L p b c 0 1 +
    (1+(k:ℝ))^3*referenceProfileMass g lam δ R L p b c

lemma referenceProfileSecondMass_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) :
    0 ≤ referenceProfileSecondMass g lam δ R L p b c := by
  exact integral_nonneg (fun x => mul_nonneg (mul_nonneg
    (referenceDensityFamily_pos g hg L (lam,x)).le (sq_nonneg _)) (fischerInner_self_nonneg _))

lemma referenceWeightedPolynomialDerivative_zero (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (x V : R3) :
    referenceWeightedPolynomialDerivative g L lam b c f 0 1 x V =
      referenceCovariantPolynomialDerivative g L lam b c x V := by
  simp only [referenceWeightedPolynomialDerivative,zero_mul,map_zero,map_one,one_mul,mul_zero,add_zero]

lemma referenceWeightedFrameEnergy_parallelogram (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (f : R3 → ℝ) (k : ℝ) (x : R3) :
    referenceWeightedFrameEnergy g L lam b c f k 1 x + referenceWeightedFrameEnergy g L lam b c f k (-1) x =
      2*referenceWeightedFrameEnergy g L lam b c f 0 1 x +
      2*k^2*metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x^2*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) := by
  have hi (i : Fin 3) : fischerInner
      (referenceWeightedPolynomialDerivative g L lam b c f k 1 x (referenceMetricGramFrame g L (lam,x) i))
      (referenceWeightedPolynomialDerivative g L lam b c f k 1 x (referenceMetricGramFrame g L (lam,x) i)) +
      fischerInner
      (referenceWeightedPolynomialDerivative g L lam b c f k (-1) x (referenceMetricGramFrame g L (lam,x) i))
      (referenceWeightedPolynomialDerivative g L lam b c f k (-1) x (referenceMetricGramFrame g L (lam,x) i)) =
      2*fischerInner (referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i))
        (referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i)) +
      2*k^2*(fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i))^2*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) := by
    simp only [referenceWeightedPolynomialDerivative,fischerInner_weighted_square]
    ring
  rw [referenceMetricDifferentialNorm_sq_eq_frame_sum g hg L lam f x]
  simp only [referenceWeightedFrameEnergy,← Finset.sum_add_distrib]
  simp_rw [hi,referenceWeightedPolynomialDerivative_zero]
  simp only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]

lemma referenceProfileFrameEnergy_parallelogram (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (k : ℝ) :
    referenceProfileFrameEnergy g lam δ R L p b c k 1 + referenceProfileFrameEnergy g lam δ R L p b c k (-1) =
      2*referenceProfileFrameEnergy g lam δ R L p b c 0 1 + 2*k^2*referenceProfileSecondMass g lam δ R L p b c := by
  let f := referenceLogRadius δ R p L
  let rho := fun x : R3 => referenceDensityFamily g L (lam,x)
  have hf := contDiff_log_referenceRadius δ R p L hδ hR
  have hr : Continuous rho := ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hp := integrable_referenceWeightedFrameEnergy g hg L lam rho hr b c f k 1 hc hf hcompact
  have hm := integrable_referenceWeightedFrameEnergy g hg L lam rho hr b c f k (-1) hc hf hcompact
  have hG := integrable_referenceWeightedFrameEnergy g hg L lam rho hr b c f 0 1 hc hf hcompact
  have hV : Integrable (fun x => rho x*referenceProfileNorm g lam δ R p L x^2*
      fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
    simpa only [rho,Pi.pow_apply] using integrable_referenceDensity_weighted_fischerPair g hg L lam _
      ((continuous_referenceProfileNorm g hg lam δ R L p hδ hR).pow 2) b b c c hc hc hcompact
  rw [referenceProfileFrameEnergy,referenceProfileFrameEnergy,← integral_add hp hm]
  calc
    _ = ∫ x : R3, 2*(rho x*referenceWeightedFrameEnergy g L lam b c f 0 1 x)+
        (2*k^2)*(rho x*referenceProfileNorm g lam δ R p L x^2*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hh := referenceWeightedFrameEnergy_parallelogram g hg L lam b c f k x
      unfold referenceProfileNorm
      dsimp only [f,rho] at *
      nlinarith only [congrArg (fun z : ℝ => referenceDensityFamily g L (lam,x)*z) hh]
    _ = _ := by
      rw [integral_add (hG.const_mul _) (hV.const_mul _)]
      simp only [integral_const_mul,referenceProfileFrameEnergy,referenceProfileSecondMass,f,rho]

lemma referenceProfileFrameEnergy_controls_gradient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (L c0 nu J1 J2 D : ℝ) (hnu : 0 < nu)
    (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p k : ℕ) (hp : 1 ≤ p)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0) :
    referenceProfileFrameEnergy g lam δ R L p b c 0 1 +
      (k:ℝ)^2*referenceProfileSecondMass g lam δ R L p b c ≤ referenceProfileFrameEnergy g lam δ R L p b c k 1 := by
  have hpar := referenceProfileFrameEnergy_parallelogram g hg lam δ R L p hδ hR b c hc hcompact k
  have hthird := referenceProfileFrameEnergy_square_difference g hg L lam δ R p k hδ hR b c hc hcompact
  have htrace := referenceProfileTraceHessianEnergy_le g hg K L c0 nu J1 J2 D hbounds lam hlam δ hδ hδ1 R hR p hp k b c hc hcompact hzero
  have hM := referenceProfileMass_nonneg g hg lam δ R L p b c
  have hsign : referenceProfileTraceHessianEnergy g lam δ R L p b c k ≤ 0 := by
    have hh : 0 ≤ 6*nu*(k:ℝ)*referenceProfileMass g lam δ R L p b c := by positivity
    linarith only [htrace,hh]
  change referenceProfileFrameEnergy g lam δ R L p b c k (-1) =
    referenceProfileFrameEnergy g lam δ R L p b c k 1 + referenceProfileTraceHessianEnergy g lam δ R L p b c k at hthird
  linarith

lemma referenceWeightedFrameEnergy_gradient_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (f : R3 → ℝ) (k : ℝ) (x : R3) :
    referenceWeightedFrameEnergy g L lam b c f 0 1 x ≤
      2*referenceWeightedFrameEnergy g L lam b c f k 1 x +
      2*k^2*metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x^2*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) := by
  have hi (i : Fin 3) : fischerInner
      (referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i))
      (referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i)) ≤
      2*fischerInner
      (referenceWeightedPolynomialDerivative g L lam b c f k 1 x (referenceMetricGramFrame g L (lam,x) i))
      (referenceWeightedPolynomialDerivative g L lam b c f k 1 x (referenceMetricGramFrame g L (lam,x) i)) +
      2*k^2*(fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i))^2*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) := by
    let q := referenceWeightedPolynomialDerivative g L lam b c f k 1 x (referenceMetricGramFrame g L (lam,x) i)
    let w := k*fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i)
    have hrel : q+C (-w)*finitePolynomialField b c x =
        referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i) := by
      simp only [q,w,referenceWeightedPolynomialDerivative,map_one,one_mul,map_neg]
      ring
    have hh := fischerInner_self_add_le q (C (-w)*finitePolynomialField b c x)
    rw [hrel] at hh
    simp only [fischerInner_C_mul_left,fischerInner_C_mul_right] at hh
    apply hh.trans_eq
    dsimp only [q,w]
    ring
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hzero : referenceWeightedFrameEnergy g L lam b c f 0 1 x = ∑ i : Fin 3,
      fischerInner (referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i))
        (referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i)) := by
    simp only [referenceWeightedFrameEnergy,referenceWeightedPolynomialDerivative_zero]
  rw [hzero]
  apply hh.trans_eq
  rw [referenceMetricDifferentialNorm_sq_eq_frame_sum g hg L lam f x]
  simp only [referenceWeightedFrameEnergy,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]

lemma referenceProfileWeightedFrameEnergy_controls_gradient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (k : ℝ) :
    referenceProfileWeightedFrameEnergy g lam δ R L p b c 0 1 ≤
      2*referenceProfileWeightedFrameEnergy g lam δ R L p b c k 1 +
      2*k^2*referenceProfileMass g lam δ R L p b c := by
  let f := referenceLogRadius δ R p L
  let rho := fun x : R3 => referenceDensityFamily g L (lam,x)
  let beta := referenceProfileNorm g lam δ R p L
  have hG := integrable_referenceProfileNorm_inv_frameEnergy g hg lam δ R L p hδ hR hL hp b c 0 1 hc hcompact
  have hW := integrable_referenceProfileNorm_inv_frameEnergy g hg lam δ R L p hδ hR hL hp b c k 1 hc hcompact
  have hM := integrable_referenceProfileNorm_fischerSquare g hg lam δ R L p hδ hR b c hc hcompact
  have hh : referenceProfileWeightedFrameEnergy g lam δ R L p b c 0 1 ≤
      ∫ x : R3, 2*(rho x*(beta x)⁻¹*referenceWeightedFrameEnergy g L lam b c f k 1 x)+
        (2*k^2)*(rho x*beta x*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
    apply integral_mono hG ((hW.const_mul _).add (hM.const_mul _))
    intro x
    have hbeta : 0 < beta x := referenceProfileNorm_pos g hg lam δ R L p hδ hR hL hp x
    have hpoint := mul_le_mul_of_nonneg_left (referenceWeightedFrameEnergy_gradient_bound g hg L lam b c f k x)
      (show 0 ≤ rho x*(beta x)⁻¹ from mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le (inv_nonneg.mpr hbeta.le))
    apply hpoint.trans_eq
    change rho x*(beta x)⁻¹*(2*referenceWeightedFrameEnergy g L lam b c f k 1 x+
      2*k^2*(beta x)^2*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) =
      2*(rho x*(beta x)⁻¹*referenceWeightedFrameEnergy g L lam b c f k 1 x)+
      (2*k^2)*(rho x*beta x*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x))
    field_simp [hbeta.ne']
    <;> ring
  apply hh.trans_eq
  rw [integral_add (hW.const_mul _) (hM.const_mul _)]
  simp only [integral_const_mul,referenceProfileWeightedFrameEnergy,referenceProfileMass,rho,beta,f]

theorem referenceProfileModeFischerEnergy_le (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (L c0 nu J1 J2 D : ℝ) (hL : 0 < L) (hnu : 0 < nu)
    (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0) :
    referenceProfileModeFischerEnergy g lam δ R L p k b c ≤
      4*referenceProfileFrameEnergy g lam δ R L p b c k 1 +
      4*(k:ℝ)*referenceProfileWeightedFrameEnergy g lam δ R L p b c k 1 +
      12*(k:ℝ)^3*referenceProfileMass g lam δ R L p b c := by
  let n : ℝ := k
  let G := referenceProfileFrameEnergy g lam δ R L p b c 0 1
  let V := referenceProfileSecondMass g lam δ R L p b c
  let I := referenceProfileWeightedFrameEnergy g lam δ R L p b c 0 1
  let M := referenceProfileMass g lam δ R L p b c
  let X := referenceProfileFrameEnergy g lam δ R L p b c k 1
  let W := referenceProfileWeightedFrameEnergy g lam δ R L p b c k 1
  have hn : 1 ≤ n := by change (1:ℝ) ≤ (k:ℝ); exact_mod_cast hk
  have hn0 : 0 ≤ n := by linarith
  have hG : 0 ≤ G := referenceProfileFrameEnergy_nonneg g hg lam δ R L p b c 0 1
  have hV : 0 ≤ V := referenceProfileSecondMass_nonneg g hg lam δ R L p b c
  have hI : 0 ≤ I := referenceProfileWeightedFrameEnergy_nonneg g hg lam δ R L p b c 0 1
  have hM : 0 ≤ M := referenceProfileMass_nonneg g hg lam δ R L p b c
  have hplain : G+n^2*V ≤ X := referenceProfileFrameEnergy_controls_gradient g hg K L c0 nu J1 J2 D hnu hbounds lam hlam δ hδ hδ1 R hR p k hp b c hc hcompact hzero
  have hweight : I ≤ 2*W+2*n^2*M := referenceProfileWeightedFrameEnergy_controls_gradient g hg lam δ R L p hδ hR hL hp b c hc hcompact k
  have hfac : 1+n ≤ 2*n := by linarith
  have hfac2 : (1+n)^2 ≤ 4*n^2 := by nlinarith
  have hpart1 : G+(1+n)^2*V ≤ 4*X := by
    have hh := mul_le_mul_of_nonneg_right hfac2 hV
    linarith only [hh,hplain,hG]
  have hpart2 : (1+n)*I ≤ 4*n*W+4*n^3*M := by
    have hh := mul_le_mul_of_nonneg_right hfac hI
    have hw := mul_le_mul_of_nonneg_left hweight (show 0 ≤ 2*n by positivity)
    nlinarith only [hh,hw]
  have hpart3 : (1+n)^3*M ≤ 8*n^3*M := by
    calc
      _ ≤ (2*n)^3*M := by gcongr
      _ = _ := by ring
  change G+(1+n)^2*V+(1+n)*I+(1+n)^3*M ≤ 4*X+4*n*W+12*n^3*M
  linarith

def referenceFiberPolynomialSquare (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (U : MvPolynomial (Fin 3) ℝ) : ℝ :=
  ∫ v : R3, (metricFramePolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
    (referenceMetricGramFrame g L (lam,x)) U v)^2
    ∂metricFrameProbability (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
      (referenceMetricGramFrame g L (lam,x)) (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x))

lemma referenceFiberPolynomialSquare_eq (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (k : ℕ)
    (U : MvPolynomial (Fin 3) ℝ) (hU : U ∈ harmonicHomogeneous k) :
    referenceFiberPolynomialSquare g hg L lam x U = fischerInner U U / sphereNormalization 3 k := by
  simpa only [referenceFiberPolynomialSquare,pow_two,normalizedFischerInner,Fintype.card_fin] using
    reference_metricFramePolynomial_fiber_inner hF g hg L lam x k U U hU hU

def referenceProfileModeEnergyDensity (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p k : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x : R3) : ℝ :=
  let U := finitePolynomialField b c x
  let Q := fun i : Fin 3 => referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i)
  let V := referenceFiberPolynomialSquare g hg L lam x U
  let G := referenceFiberCovectorPair g hg L lam x Q Q
  let beta := referenceProfileNorm g lam δ R p L x
  G+beta^2*(1+(k:ℝ))^2*V+beta⁻¹*(1+(k:ℝ))*G+beta*(1+(k:ℝ))^3*V

def referenceProfileModeEnergy (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p k : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*referenceProfileModeEnergyDensity g hg lam δ R L p k b c x

lemma referenceProfileModeEnergyDensity_eq (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (x : R3) :
    referenceProfileModeEnergyDensity g hg lam δ R L p k b c x =
      (referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) 0 1 x +
        (1+(k:ℝ))^2*referenceProfileNorm g lam δ R p L x^2*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) +
        (1+(k:ℝ))*(referenceProfileNorm g lam δ R p L x)⁻¹*referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) 0 1 x +
        (1+(k:ℝ))^3*referenceProfileNorm g lam δ R p L x*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) /
      sphereNormalization 3 k := by
  let Q := fun i : Fin 3 => referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i)
  have hQ : ∀ i, Q i ∈ harmonicHomogeneous k := fun i =>
    referenceCovariantPolynomialDerivative_harmonicHomogeneous g hg L lam k hk b hb c x (referenceMetricGramFrame g L (lam,x) i)
  dsimp only [referenceProfileModeEnergyDensity]
  rw [referenceFiberPolynomialSquare_eq hF g hg L lam x k _ (finitePolynomialField_harmonicHomogeneous k b hb c x),
    referenceFiberCovectorPair_eq hF g hg L lam x k Q Q hQ hQ]
  simp only [referenceWeightedFrameEnergy,referenceWeightedPolynomialDerivative_zero]
  dsimp only [Q]
  ring

theorem referenceProfileModeEnergy_integrable_and_eq (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p k : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*referenceProfileModeEnergyDensity g hg lam δ R L p k b c x) ∧
      referenceProfileModeEnergy g hg lam δ R L p k b c = referenceProfileModeFischerEnergy g lam δ R L p k b c / sphereNormalization 3 k := by
  let f := referenceLogRadius δ R p L
  let rho := fun x : R3 => referenceDensityFamily g L (lam,x)
  let beta := referenceProfileNorm g lam δ R p L
  let A := fun x : R3 => rho x*referenceWeightedFrameEnergy g L lam b c f 0 1 x
  let B := fun x : R3 => rho x*(beta x)^2*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)
  let C := fun x : R3 => rho x*(beta x)⁻¹*referenceWeightedFrameEnergy g L lam b c f 0 1 x
  let D := fun x : R3 => rho x*beta x*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)
  have hf := contDiff_log_referenceRadius δ R p L hδ hR
  have hr : Continuous rho := ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hA : Integrable A := integrable_referenceWeightedFrameEnergy g hg L lam rho hr b c f 0 1 hc hf hcompact
  have hB : Integrable B := by
    simpa only [B,rho,beta,Pi.pow_apply] using integrable_referenceDensity_weighted_fischerPair g hg L lam _
      ((continuous_referenceProfileNorm g hg lam δ R L p hδ hR).pow 2) b b c c hc hc hcompact
  have hC : Integrable C := integrable_referenceProfileNorm_inv_frameEnergy g hg lam δ R L p hδ hR hL hp b c 0 1 hc hcompact
  have hD : Integrable D := integrable_referenceProfileNorm_fischerSquare g hg lam δ R L p hδ hR b c hc hcompact
  have hAB : Integrable (fun x => A x+(1+(k:ℝ))^2*B x) :=
    hA.add (hB.const_mul ((1+(k:ℝ))^2))
  have hABC : Integrable (fun x => (A x+(1+(k:ℝ))^2*B x)+(1+(k:ℝ))*C x) :=
    hAB.add (hC.const_mul (1+(k:ℝ)))
  have hraw : Integrable (fun x => ((A x+(1+(k:ℝ))^2*B x)+(1+(k:ℝ))*C x)+(1+(k:ℝ))^3*D x) :=
    hABC.add (hD.const_mul ((1+(k:ℝ))^3))
  have heq (x : R3) : rho x*referenceProfileModeEnergyDensity g hg lam δ R L p k b c x =
      (((A x+(1+(k:ℝ))^2*B x)+(1+(k:ℝ))*C x)+(1+(k:ℝ))^3*D x)/sphereNormalization 3 k := by
    rw [referenceProfileModeEnergyDensity_eq hF g hg lam δ R L p k hk b hb c x]
    dsimp only [A,B,C,D,rho,beta,f]
    ring
  have hactual : Integrable (fun x => referenceDensityFamily g L (lam,x)*referenceProfileModeEnergyDensity g hg lam δ R L p k b c x) :=
    (hraw.div_const (sphereNormalization 3 k)).congr (Filter.Eventually.of_forall (fun x => (heq x).symm))
  refine ⟨hactual,?_⟩
  calc
    _ = (∫ x : R3, ((A x+(1+(k:ℝ))^2*B x)+(1+(k:ℝ))*C x)+(1+(k:ℝ))^3*D x)/sphereNormalization 3 k := by
      rw [referenceProfileModeEnergy,← integral_div]
      exact integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = _ := by
      rw [integral_add hABC (hD.const_mul _)]
      change ((∫ x : R3, (A x+(1+(k:ℝ))^2*B x)+(1+(k:ℝ))*C x)+
        (∫ x : R3, (1+(k:ℝ))^3*D x))/sphereNormalization 3 k = _
      rw [integral_add hAB (hC.const_mul _)]
      change (((∫ x : R3, A x+(1+(k:ℝ))^2*B x)+(∫ x : R3, (1+(k:ℝ))*C x))+
        (∫ x : R3, (1+(k:ℝ))^3*D x))/sphereNormalization 3 k = _
      rw [integral_add hA (hB.const_mul _)]
      simp only [integral_const_mul,referenceProfileModeFischerEnergy,referenceProfileFrameEnergy,
        referenceProfileSecondMass,referenceProfileWeightedFrameEnergy,referenceProfileMass,A,B,C,D,rho,beta,f]

def referenceProfileCoercivityConstant (a nu : ℝ) : ℝ :=
  min (1/8:ℝ) (min (a/16) (nu/12))

lemma referenceProfileCoercivityConstant_pos (a nu : ℝ) (ha : 0 < a) (hnu : 0 < nu) :
    0 < referenceProfileCoercivityConstant a nu := by
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

lemma referenceProfileCoercivityConstant_le (a nu : ℝ) :
    referenceProfileCoercivityConstant a nu ≤ 1/8 ∧
    referenceProfileCoercivityConstant a nu ≤ a/16 ∧ referenceProfileCoercivityConstant a nu ≤ nu/12 :=
  ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩

theorem referenceProfileModeEnergy_coercive (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsClosed K)
    (L c0 nu J1 J2 D : ℝ) (hL : 0 < L) (hnu : 0 < nu)
    (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p : ℕ) (hp : 1 ≤ p) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0)
    (a beta0 Ccurv : ℝ) (ha : 0 < a) (hb0 : 1 ≤ beta0) (hC : 0 ≤ Ccurv)
    (hasmall : a ≤ nu/8) (hab : a ≤ beta0) (habsorb : 50*Ccurv ≤ nu*beta0)
    (hbeta : ∀ x ∈ K, beta0 ≤ referenceProfileNorm g lam δ R p L x)
    (hcurv : |referenceIntegratedFullCovectorCurvature g L lam b c| ≤
      Ccurv*((m:ℝ)+1)^2*referenceFischerMass g L lam b c) :
    referenceProfileCoercivityConstant a nu * referenceProfileModeEnergy g hg lam δ R L p (m+1) b c ≤
      referenceRaisingEnergy g L lam b c (referenceLogRadius δ R p L) m -
        referenceLoweringEnergy g L lam b c (referenceLogRadius δ R p L) m := by
  let n : ℝ := (m:ℝ)+1
  let X := referenceProfileFrameEnergy g lam δ R L p b c (m+1) 1
  let W := referenceProfileWeightedFrameEnergy g lam δ R L p b c (m+1) 1
  let M := referenceProfileMass g lam δ R L p b c
  let Raw := referenceProfileModeFischerEnergy g lam δ R L p (m+1) b c
  let E := referenceProfileModeEnergy g hg lam δ R L p (m+1) b c
  let N := sphereNormalization 3 (m+1)
  let Δ := referenceRaisingEnergy g L lam b c (referenceLogRadius δ R p L) m-
    referenceLoweringEnergy g L lam b c (referenceLogRadius δ R p L) m
  let C := referenceProfileCoercivityConstant a nu
  have hCpos : 0 < C := referenceProfileCoercivityConstant_pos a nu ha hnu
  have hN : 0 < N := sphereNormalization_pos (n:=3) (by norm_num) (m+1)
  have hn : 0 ≤ n := by positivity
  have hX : 0 ≤ X := referenceProfileFrameEnergy_nonneg g hg lam δ R L p b c (m+1) 1
  have hW : 0 ≤ W := referenceProfileWeightedFrameEnergy_nonneg g hg lam δ R L p b c (m+1) 1
  have hM : 0 ≤ M := referenceProfileMass_nonneg g hg lam δ R L p b c
  have heq : E = Raw/N := (referenceProfileModeEnergy_integrable_and_eq hF g hg lam δ R L p (m+1) hδ hR hL hp (by omega) b hb c hc hcompact).2
  have hnorm : Raw ≤ 4*X+4*n*W+12*n^3*M := by
    simpa only [Raw,X,W,M,n,Nat.cast_add,Nat.cast_one] using
      referenceProfileModeFischerEnergy_le g hg K L c0 nu J1 J2 D hL hnu hbounds lam hlam δ hδ hδ1 R hR p (m+1) hp (by omega) b c hc hcompact hzero
  have hgain : X/2+(a/4)*(n+2)*W+nu*n^3*M ≤ N*Δ := by
    simpa only [X,W,M,n,N,Δ,Nat.cast_add,Nat.cast_one] using
      referenceProfileRaisingEnergy_gain hF g hg K hK L c0 nu J1 J2 D hL hnu hbounds lam hlam δ hδ hδ1 R hR p hp m b hb c hc hcompact hzero a beta0 Ccurv ha hb0 hC hasmall hab habsorb hbeta hcurv
  obtain ⟨hC1,hC2,hC3⟩ := referenceProfileCoercivityConstant_le a nu
  have hcx : 4*C ≤ 1/2 := by dsimp only [C]; linarith only [hC1]
  have hcw : 4*C ≤ a/4 := by dsimp only [C]; linarith only [hC2]
  have hcm : 12*C ≤ nu := by dsimp only [C]; linarith only [hC3]
  have hreserve : C*(4*X+4*n*W+12*n^3*M) ≤ X/2+(a/4)*(n+2)*W+nu*n^3*M := by
    have hx := mul_le_mul_of_nonneg_right hcx hX
    have hw := mul_le_mul_of_nonneg_right hcw (show 0 ≤ n*W by positivity)
    have hm := mul_le_mul_of_nonneg_right hcm (show 0 ≤ n^3*M by positivity)
    have haW := mul_nonneg ha.le hW
    nlinarith only [hx,hw,hm,haW]
  have hfinal : N*(C*E) ≤ N*Δ := by
    calc
      N*(C*E) = C*Raw := by rw [heq]; field_simp [hN.ne'] <;> ring
      _ ≤ C*(4*X+4*n*W+12*n^3*M) := mul_le_mul_of_nonneg_left hnorm hCpos.le
      _ ≤ X/2+(a/4)*(n+2)*W+nu*n^3*M := hreserve
      _ ≤ N*Δ := hgain
  by_contra hnot
  have hpos : 0 < N*(C*E-Δ) := mul_pos hN (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith only [hfinal,hpos]

theorem exists_referenceProfileModeEnergy_uniform_coercivity (g : MatrixField)
    (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L cRaise : ℝ, 0 < L ∧ 0 < cRaise ∧
      ∀ ε : ℝ, 0 < ε → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
          referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x^2 ≤ ε) ∧
        ∀ (τ : Type u) [Fintype τ], ∀ hF : SphereFischerInner,
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ m : ℕ, ∀ b : τ → MvPolynomial (Fin 3) ℝ,
          (∀ j, b j ∈ harmonicHomogeneous (m+1)) →
          ∀ c : R3 → τ → ℝ, ContDiff ℝ ∞ c → HasCompactSupport c →
          (∀ x ∉ K, finitePolynomialField b c x = 0) →
          cRaise*referenceProfileModeEnergy g hg lam δ R L p (m+1) b c ≤
            referenceRaisingEnergy g L lam b c (referenceLogRadius δ R p L) m -
              referenceLoweringEnergy g L lam b c (referenceLogRadius δ R p L) m := by
  obtain ⟨L,c0,nu,J1,J2,D,hL,hc0,hnu,hJ1,hJ2,hD,hbounds⟩ := exists_referenceProfileBounds g hg K hK
  obtain ⟨A,hA,hcurv⟩ := exists_referenceIntegratedCurvature_allFinite_uniform_bound.{u} g hg L hL K hK
  let a := min (1:ℝ) (nu/8)
  let beta0 := max (1:ℝ) (50*A/nu)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hasmall : a ≤ nu/8 := min_le_right _ _
  have ha1 : a ≤ 1 := min_le_left _ _
  have hb0 : 1 ≤ beta0 := le_max_left _ _
  have hab : a ≤ beta0 := ha1.trans hb0
  have habsorb : 50*A ≤ nu*beta0 := by
    have hh := (div_le_iff₀ hnu).mp (le_max_right (1:ℝ) (50*A/nu))
    simpa only [beta0,mul_comm] using hh
  refine ⟨L,referenceProfileCoercivityConstant a nu,hL,referenceProfileCoercivityConstant_pos a nu ha hnu,?_⟩
  intro ε hε
  obtain ⟨p,hp,R,hR,hprofile⟩ := referenceProfileBounds_choose_degree_radius g K L c0 nu J1 J2 D hc0 hbounds beta0 ε hε
  refine ⟨p,hp,R,hR,?_,?_⟩
  · intro lam hlam δ hδ hδ1 x hx
    exact (hprofile lam hlam δ hδ hδ1 x hx).2
  · intro τ inst hF lam hlam δ hδ hδ1 m b hb c hc hcompact hzero
    have hhcurv : |referenceIntegratedFullCovectorCurvature g L lam b c| ≤
        A*((m:ℝ)+1)^2*referenceFischerMass g L lam b c := by
      simpa only [Nat.cast_add,Nat.cast_one] using hcurv τ hF lam hlam (m+1) (by omega) b hb c hc hcompact hzero
    exact referenceProfileModeEnergy_coercive hF g hg K hK.isClosed L c0 nu J1 J2 D hL hnu hbounds
      lam hlam δ hδ hδ1 R hR p (by omega) m b hb c hc hcompact hzero a beta0 A ha hb0 hA.le
      hasmall hab habsorb (fun x hx => (hprofile lam hlam δ hδ hδ1 x hx).1) hhcurv

end OAI.AnisotropicCalderon.FiniteProfileNormComparison
