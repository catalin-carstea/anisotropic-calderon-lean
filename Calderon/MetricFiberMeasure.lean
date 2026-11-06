import Calderon.OrthogonalSphereMeasure
import Calderon.SmoothMetricFrame
import Calderon.FrameCurvaturePolynomial

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.MetricFiberMeasure
open RadiusProfile ConformalDepth MetricOperator SphereHarmonic FrameCurvaturePolynomial
  SmoothMetricFrame OrthogonalSphereMeasure

def metricFrameSynthesis (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : R3 ≃ₗ[ℝ] R3 :=
  (PiLp.basisFun 2 ℝ (Fin 3)).equivFun.trans (metricFrameBasis M e he).equivFun.symm

lemma metricFrameSynthesis_apply (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (w : R3) :
    metricFrameSynthesis M e he w = ∑ i : Fin 3, w i • e i := by
  simp only [metricFrameSynthesis,LinearEquiv.trans_apply,Module.Basis.equivFun_symm_apply,
    Module.Basis.equivFun_apply,PiLp.basisFun_repr,metricFrameBasis_apply]

lemma metricFrameSynthesis_quadratic (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (w : R3) :
    ⟪M (metricFrameSynthesis M e he w),metricFrameSynthesis M e he w⟫_ℝ = ‖w‖ ^ 2 := by
  rw [metricFrameSynthesis_apply]
  have hgram := he
  simp only [IsMetricOrthonormalFrame] at hgram
  simp only [map_sum,map_smul,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right,hgram,EuclideanSpace.real_norm_sq_eq]
  simp [mul_ite,ite_mul,pow_two]

def metricFrameTransition (M : R3 →L[ℝ] R3) (e f : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (hf : IsMetricOrthonormalFrame M f) : R3 ≃ₗᵢ[ℝ] R3 where
  toLinearEquiv := (metricFrameSynthesis M f hf).trans (metricFrameSynthesis M e he).symm
  norm_map' w := by
    have h1 := metricFrameSynthesis_quadratic M e he
      ((metricFrameSynthesis M e he).symm (metricFrameSynthesis M f hf w))
    have h2 := metricFrameSynthesis_quadratic M f hf w
    rw [(metricFrameSynthesis M e he).apply_symm_apply] at h1
    change ‖(metricFrameSynthesis M e he).symm (metricFrameSynthesis M f hf w)‖ = ‖w‖
    nlinarith [norm_nonneg w,norm_nonneg ((metricFrameSynthesis M e he).symm (metricFrameSynthesis M f hf w))]

lemma metricFrameSynthesis_transition (M : R3 →L[ℝ] R3) (e f : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (hf : IsMetricOrthonormalFrame M f) (w : R3) :
    metricFrameSynthesis M e he (metricFrameTransition M e f he hf w) = metricFrameSynthesis M f hf w :=
  (metricFrameSynthesis M e he).apply_symm_apply _

def metricUnitFiber (M : R3 →L[ℝ] R3) : Set R3 := {v | ⟪M v,v⟫_ℝ = 1}

lemma measurableSet_metricUnitFiber (M : R3 →L[ℝ] R3) : MeasurableSet (metricUnitFiber M) :=
  (isClosed_singleton.preimage (M.continuous.inner continuous_id)).measurableSet

def metricFrameSphereMap (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : UnitSphere → R3 :=
  fun u => metricFrameSynthesis M e he u.val

lemma measurable_metricFrameSphereMap (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : Measurable (metricFrameSphereMap M e he) :=
  ((metricFrameSynthesis M e he).toContinuousLinearEquiv.continuous.comp continuous_subtype_val).measurable

lemma metricFrameSphereMap_mem_metricUnitFiber (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (u : UnitSphere) :
    metricFrameSphereMap M e he u ∈ metricUnitFiber M := by
  change ⟪M (metricFrameSynthesis M e he u.val),metricFrameSynthesis M e he u.val⟫_ℝ = 1
  rw [metricFrameSynthesis_quadratic]
  have h : ‖u.val‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using u.property
  rw [h,one_pow]

def metricFrameProbability (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : Measure R3 :=
  Measure.map (metricFrameSphereMap M e he) sphereProbability

instance metricFrameProbability_probability (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : IsProbabilityMeasure (metricFrameProbability M e he) := by
  refine ⟨?_⟩
  rw [metricFrameProbability,Measure.map_apply (measurable_metricFrameSphereMap M e he)
    MeasurableSet.univ,Set.preimage_univ,measure_univ]

theorem metricFrameProbability_metricUnitFiber_compl (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : metricFrameProbability M e he (metricUnitFiber M)ᶜ = 0 := by
  rw [metricFrameProbability,Measure.map_apply (measurable_metricFrameSphereMap M e he)
    (measurableSet_metricUnitFiber M).compl]
  have h : metricFrameSphereMap M e he ⁻¹' (metricUnitFiber M)ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u
    simpa only [Set.mem_preimage,Set.mem_compl_iff,not_not] using
      metricFrameSphereMap_mem_metricUnitFiber M e he u
  rw [h,measure_empty]

theorem metricFrameProbability_frame_independent (M : R3 →L[ℝ] R3) (e f : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (hf : IsMetricOrthonormalFrame M f) :
    metricFrameProbability M e he = metricFrameProbability M f hf := by
  let T := metricFrameTransition M e f he hf
  have hcomp : metricFrameSphereMap M e he ∘ orthogonalSphereHomeomorph T = metricFrameSphereMap M f hf := by
    funext u
    exact metricFrameSynthesis_transition M e f he hf u.val
  rw [metricFrameProbability,metricFrameProbability,← hcomp,
    ← Measure.map_map (measurable_metricFrameSphereMap M e he) (orthogonalSphereHomeomorph T).measurable,
    (orthogonalSphereHomeomorph_sphereProbability_preserving T).map_eq]

theorem reference_metricFrameProbability_frame_independent (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e) :
    metricFrameProbability (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e he =
      metricFrameProbability (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
        (referenceMetricGramFrame g L (lam,x)) (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)) :=
  metricFrameProbability_frame_independent _ _ _ he _

end OAI.AnisotropicCalderon.MetricFiberMeasure
