import Calderon.MetricFiberMeasure

noncomputable section
open MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.MetricFiberFischer
open RadiusProfile ConformalDepth MetricOperator SphereHarmonic AngularPolynomial
  FrameCurvaturePolynomial SmoothMetricFrame MetricFiberMeasure

lemma metricFrameCoordinates_synthesis (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (w : R3) :
    metricFrameCoordinates M e (metricFrameSynthesis M e he w) = w.ofLp := by
  funext i
  rw [metricFrameCoordinates_apply,metricFrameSynthesis_apply]
  have hgram := he
  simp only [IsMetricOrthonormalFrame] at hgram
  simp only [map_sum,map_smul,sum_inner,real_inner_smul_left,hgram]
  simp

lemma metricFramePolynomial_synthesis (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (p : MvPolynomial (Fin 3) ℝ) (w : R3) :
    metricFramePolynomial M e p (metricFrameSynthesis M e he w) = p.eval w.ofLp := by
  simp only [metricFramePolynomial,metricFrameCoordinates_synthesis]

theorem metricFramePolynomial_fiber_integral_pair (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (p q : MvPolynomial (Fin 3) ℝ) :
    (∫ v : R3, metricFramePolynomial M e p v * metricFramePolynomial M e q v
      ∂metricFrameProbability M e he) = ⟪polynomialSphereL2 p,polynomialSphereL2 q⟫_ℝ := by
  have hcont : Continuous (fun v : R3 => metricFramePolynomial M e p v * metricFramePolynomial M e q v) :=
    (contDiff_metricFramePolynomial M e p).continuous.mul
      (contDiff_metricFramePolynomial M e q).continuous
  rw [metricFrameProbability,integral_map_of_stronglyMeasurable
    (measurable_metricFrameSphereMap M e he) hcont.stronglyMeasurable,polynomialSphereL2_inner]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [metricFrameSphereMap,metricFramePolynomial_synthesis]

theorem integrable_metricFramePolynomial_fiber_pair (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (p q : MvPolynomial (Fin 3) ℝ) :
    Integrable (fun v : R3 => metricFramePolynomial M e p v * metricFramePolynomial M e q v)
      (metricFrameProbability M e he) := by
  have hcont : Continuous (fun v : R3 => metricFramePolynomial M e p v * metricFramePolynomial M e q v) :=
    (contDiff_metricFramePolynomial M e p).continuous.mul (contDiff_metricFramePolynomial M e q).continuous
  rw [metricFrameProbability]
  apply (integrable_map_measure hcont.stronglyMeasurable.aestronglyMeasurable
    (measurable_metricFrameSphereMap M e he).aemeasurable).2
  change Integrable (fun u : UnitSphere =>
    metricFramePolynomial M e p (metricFrameSphereMap M e he u) *
    metricFramePolynomial M e q (metricFrameSphereMap M e he u)) sphereProbability
  have h : Integrable (fun u : UnitSphere => p.eval u.val.ofLp * q.eval u.val.ofLp)
      sphereProbability :=
    ((polynomialSphere p).continuous.mul (polynomialSphere q).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simpa only [Function.comp_apply,metricFrameSphereMap,metricFramePolynomial_synthesis] using h

theorem metricFramePolynomial_fiber_inner (hF : SphereFischerInner)
    (M : R3 →L[ℝ] R3) (e : Fin 3 → R3) (he : IsMetricOrthonormalFrame M e) (k : ℕ)
    (p q : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) (hq : q ∈ harmonicHomogeneous k) :
    (∫ v : R3, metricFramePolynomial M e p v * metricFramePolynomial M e q v
      ∂metricFrameProbability M e he) = normalizedFischerInner k p q := by
  rw [metricFramePolynomial_fiber_integral_pair,hF k p q hp hq]

theorem metricFramePolynomial_fiber_square (hF : SphereFischerInner)
    (M : R3 →L[ℝ] R3) (e : Fin 3 → R3) (he : IsMetricOrthonormalFrame M e) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    (∫ v : R3, (metricFramePolynomial M e p v)^2 ∂metricFrameProbability M e he) =
      normalizedFischerSquare k p := by
  simpa only [pow_two,normalizedFischerSquare] using
    metricFramePolynomial_fiber_inner hF M e he k p p hp hp

theorem reference_metricFramePolynomial_fiber_inner (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (k : ℕ)
    (p q : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) (hq : q ∈ harmonicHomogeneous k) :
    (∫ v : R3,
      metricFramePolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
        (referenceMetricGramFrame g L (lam,x)) p v *
      metricFramePolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
        (referenceMetricGramFrame g L (lam,x)) q v
      ∂metricFrameProbability (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
        (referenceMetricGramFrame g L (lam,x))
        (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x))) =
      normalizedFischerInner k p q :=
  metricFramePolynomial_fiber_inner hF _ _ _ k p q hp hq

end OAI.AnisotropicCalderon.MetricFiberFischer
