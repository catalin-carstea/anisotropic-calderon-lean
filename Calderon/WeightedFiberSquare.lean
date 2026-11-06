import Calderon.WeightedFischerSquare
import Calderon.AllDegreeCovectorTransport

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.WeightedFiberSquare
open RadiusProfile ConformalDepth AngularPolynomial SphereHarmonic
  MovingFrameConnection FischerConnectionTransport FischerDensityIntegration
  WeightedFischerSquare AllDegreeCovectorTransport MetricFiberAdjunction
  SmoothMetricFrame ReferenceDensityBounds

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  MetricOperator.metricOperatorField referenceMetric dilatedMetric

variable {ι : Type*} [Fintype ι]

lemma referenceWeightedPolynomialDerivative_harmonicHomogeneous_all
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous m)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s : ℝ) (x V : R3) :
    referenceWeightedPolynomialDerivative g L lam b c f k s x V ∈ harmonicHomogeneous m := by
  apply (harmonicHomogeneous m).add_mem
  · simpa only [smul_eq_C_mul] using (harmonicHomogeneous m).smul_mem s
      (referenceCovariantPolynomialDerivative_harmonicHomogeneous_all g hg L lam m b hb c x V)
  · simpa only [smul_eq_C_mul] using (harmonicHomogeneous m).smul_mem
      (k*fderiv ℝ f x V) (finitePolynomialField_harmonicHomogeneous m b hb c x)

def referenceWeightedFiberFrameEnergy (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (x : R3) : ℝ :=
  ∑ i : Fin 3, referenceFiberPolynomialPair g hg L lam x
    (referenceWeightedPolynomialDerivative g L lam b c f k s x (referenceMetricGramFrame g L (lam,x) i))
    (referenceWeightedPolynomialDerivative g L lam b c f k s x (referenceMetricGramFrame g L (lam,x) i))

lemma referenceWeightedFiberFrameEnergy_eq (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous m)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s : ℝ) (x : R3) :
    referenceWeightedFiberFrameEnergy g hg L lam b c f k s x =
      referenceWeightedFrameEnergy g L lam b c f k s x / sphereNormalization 3 m := by
  have hp (i : Fin 3) := referenceWeightedPolynomialDerivative_harmonicHomogeneous_all
    g hg L lam m b hb c f k s x (referenceMetricGramFrame g L (lam,x) i)
  have hpair (i : Fin 3) := referenceFiberPolynomialPair_eq hF g hg L lam x m _ _ (hp i) (hp i)
  simp only [referenceWeightedFiberFrameEnergy,referenceWeightedFrameEnergy,hpair,
    normalizedFischerInner,Fintype.card_fin,Finset.sum_div]

lemma integrable_referenceWeightedFiberFrameEnergy (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (rho : R3 → ℝ) (hr : Continuous rho)
    (m : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous m)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    Integrable (fun x => rho x*referenceWeightedFiberFrameEnergy g hg L lam b c f k s x) := by
  have h := integrable_referenceWeightedFrameEnergy g hg L lam rho hr b c f k s hc hf hcompact
  have he : (fun x => rho x*referenceWeightedFiberFrameEnergy g hg L lam b c f k s x) =
      fun x => (sphereNormalization 3 m)⁻¹ * (rho x*referenceWeightedFrameEnergy g L lam b c f k s x) := by
    funext x
    rw [referenceWeightedFiberFrameEnergy_eq hF g hg L lam m b hb c f k s]
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  exact h.const_mul _

lemma integral_referenceWeightedFiberFrameEnergy_eq (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (rho : R3 → ℝ)
    (m : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous m)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s : ℝ) :
    (∫ x : R3, rho x*referenceWeightedFiberFrameEnergy g hg L lam b c f k s x) =
      (sphereNormalization 3 m)⁻¹ *
        (∫ x : R3, rho x*referenceWeightedFrameEnergy g L lam b c f k s x) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [referenceWeightedFiberFrameEnergy_eq hF g hg L lam m b hb c f k s]
  simp only [div_eq_mul_inv]
  ring

theorem compact_referenceWeightedFiberFrameEnergy_hessian_square_difference
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (k : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      referenceWeightedFiberFrameEnergy g hg L lam b c f (k : ℝ) (-1) x) =
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      referenceWeightedFiberFrameEnergy g hg L lam b c f (k : ℝ) 1 x) +
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      (2*(k : ℝ)*∑ i : Fin 3, coordinateHessian f
        (fun X Y => referenceConnectionFamily g L (lam,x) X Y) x
        (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) i)) *
      referenceFiberPolynomialPair g hg L lam x (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
  have h := compact_referenceWeightedFrameEnergy_hessian_square_difference g hg L lam b c f
    (k : ℝ) hc hf hcompact
  simp only [integral_referenceWeightedFiberFrameEnergy_eq hF g hg L lam _ k b hb c f]
  have hJ : (∫ x : R3, referenceDensityFamily g L (lam,x) *
      (2*(k : ℝ)*∑ i : Fin 3, coordinateHessian f
        (fun X Y => referenceConnectionFamily g L (lam,x) X Y) x
        (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) i)) *
      referenceFiberPolynomialPair g hg L lam x (finitePolynomialField b c x) (finitePolynomialField b c x)) =
    (sphereNormalization 3 k)⁻¹ *
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      (2*(k : ℝ)*∑ i : Fin 3, coordinateHessian f
        (fun X Y => referenceConnectionFamily g L (lam,x) X Y) x
        (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) i)) *
      fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [referenceFiberPolynomialPair_finite hF g hg L lam k b b hb hb c c]
    simp only [div_eq_mul_inv]
    ring
  rw [hJ,h,mul_add]

theorem compact_referenceLogRadius_weightedFiberFrameEnergy_square_difference
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ)
    (profileP k : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) * referenceWeightedFiberFrameEnergy g hg L lam b c
      (referenceLogRadius δ R profileP L) (k : ℝ) (-1) x) =
    (∫ x : R3, referenceDensityFamily g L (lam,x) * referenceWeightedFiberFrameEnergy g hg L lam b c
      (referenceLogRadius δ R profileP L) (k : ℝ) 1 x) +
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      (2*(k : ℝ)*∑ i : Fin 3, coordinateHessian (referenceLogRadius δ R profileP L)
        (fun X Y => referenceConnectionFamily g L (lam,x) X Y) x
        (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) i)) *
      referenceFiberPolynomialPair g hg L lam x (finitePolynomialField b c x) (finitePolynomialField b c x)) :=
  compact_referenceWeightedFiberFrameEnergy_hessian_square_difference hF g hg L lam k b hb c
    (referenceLogRadius δ R profileP L) hc (contDiff_log_referenceRadius δ R profileP L hδ hR) hcompact

end OAI.AnisotropicCalderon.WeightedFiberSquare
