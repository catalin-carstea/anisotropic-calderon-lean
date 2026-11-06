import Calderon.MetricFrameOperator
import Calderon.NormalizedGeodesicMetric

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError
open NormalCoordinatesFrame

def framedEndpointParameter (F : R3 → R3 →L[ℝ] R3) (p : (R3 × ℝ) × R3) : (R3 × ℝ) × R3 :=
  (p.1,F p.1.1 p.2)

def framedScaledEndpoint (Θ : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3) :
    (R3 × ℝ) × R3 → R3 := fun p => scaledEndpoint Θ (framedEndpointParameter F p)

def framedNormalizedEndpointDerivative (Θ : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3)
    (p : (R3 × ℝ) × R3) : R3 →L[ℝ] R3 :=
  (normalizedEndpointDerivative Θ (framedEndpointParameter F p)).comp (F p.1.1)

def framedNormalizedEndpointMetric (Θ : R3 × R3 → R3) (M F : R3 → R3 →L[ℝ] R3)
    (p : (R3 × ℝ) × R3) : R3 →L[ℝ] R3 :=
  (F p.1.1).adjoint.comp ((normalizedEndpointMetric Θ M (framedEndpointParameter F p)).comp (F p.1.1))

theorem contDiff_framedEndpointParameter (F : R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (framedEndpointParameter F) :=
  contDiff_fst.prodMk ((hF.comp contDiff_fst.fst).clm_apply contDiff_snd)

theorem contDiff_framedScaledEndpoint (Θ : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (framedScaledEndpoint Θ F) :=
  (contDiff_scaledEndpoint Θ hΘ).comp (contDiff_framedEndpointParameter F hF)

theorem contDiff_framedNormalizedEndpointDerivative (Θ : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (framedNormalizedEndpointDerivative Θ F) :=
  ((contDiff_normalizedEndpointDerivative Θ hΘ).comp (contDiff_framedEndpointParameter F hF)).clm_comp
    (hF.comp contDiff_fst.fst)

theorem contDiff_framedNormalizedEndpointMetric (Θ : R3 × R3 → R3) (M F : R3 → R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (hM : ContDiff ℝ ∞ M) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (framedNormalizedEndpointMetric Θ M F) := by
  have hA : ContDiff ℝ ∞ (fun L : R3 →L[ℝ] R3 => L.adjoint) :=
    (ContinuousLinearMap.adjoint : (R3 →L[ℝ] R3) ≃ₗᵢ[ℝ] (R3 →L[ℝ] R3)).contDiff
  exact (hA.comp (hF.comp contDiff_fst.fst)).clm_comp
    (((contDiff_normalizedEndpointMetric Θ M hΘ hM).comp
      (contDiff_framedEndpointParameter F hF)).clm_comp (hF.comp contDiff_fst.fst))

theorem framedNormalizedEndpointMetric_inner (Θ : R3 × R3 → R3) (M F : R3 → R3 →L[ℝ] R3)
    (p : (R3 × ℝ) × R3) (u v : R3) :
    inner ℝ (framedNormalizedEndpointMetric Θ M F p u) v =
      inner ℝ (M (framedScaledEndpoint Θ F p) (framedNormalizedEndpointDerivative Θ F p u))
        (framedNormalizedEndpointDerivative Θ F p v) := by
  change inner ℝ ((F p.1.1).adjoint
    (normalizedEndpointMetric Θ M (framedEndpointParameter F p) (F p.1.1 u))) v = _
  rw [ContinuousLinearMap.adjoint_inner_left,normalizedEndpointMetric_inner]
  rfl

theorem hasFDerivAt_framedScaledEndpoint_slice (Θ : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (y z : R3) (r : ℝ) :
    HasFDerivAt (fun w => Θ (y,r • F y w))
      (r • framedNormalizedEndpointDerivative Θ F ((y,r),z)) z := by
  have h := (hasFDerivAt_scaledEndpoint_slice Θ hΘ y (F y z) r).comp z (F y).hasFDerivAt
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro u
    simp [framedNormalizedEndpointDerivative,framedEndpointParameter]

theorem framedScaledEndpoint_pullback_inner (Θ : R3 × R3 → R3) (M F : R3 → R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (y z u v : R3) (r : ℝ) :
    inner ℝ (M (Θ (y,r • F y z)) (fderiv ℝ (fun w => Θ (y,r • F y w)) z u))
      (fderiv ℝ (fun w => Θ (y,r • F y w)) z v) =
      r^2 * inner ℝ (framedNormalizedEndpointMetric Θ M F ((y,r),z) u) v := by
  rw [(hasFDerivAt_framedScaledEndpoint_slice Θ F hΘ y z r).fderiv,
    framedNormalizedEndpointMetric_inner]
  simp [framedScaledEndpoint,framedEndpointParameter,scaledEndpoint,
    real_inner_smul_left,real_inner_smul_right,pow_two,mul_assoc]

theorem framedNormalizedEndpointMetric_zero (Θ : R3 × R3 → R3) (M : R3 → R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (y z : R3) (hzero : Θ (y,0) = y)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0))
    (he : IsMetricOrthonormalFrame (M y) (e y)) :
    framedNormalizedEndpointMetric Θ M (fun x => frameOperator (e x)) ((y,0),z) =
      ContinuousLinearMap.id ℝ R3 := by
  change (frameOperator (e y)).adjoint.comp
    ((normalizedEndpointMetric Θ M ((y,0),frameOperator (e y) z)).comp (frameOperator (e y))) = _
  rw [normalizedEndpointMetric_zero Θ M y _ hzero hD]
  exact frameOperator_pullback_metric (M y) (e y) he

theorem hasDerivAt_framedNormalizedEndpointMetric_zero (Θ : R3 × R3 → R3)
    (M F : R3 → R3 →L[ℝ] R3) (y z : R3)
    (hzero : HasDerivAt (fun r : ℝ => normalizedEndpointMetric Θ M ((y,r),F y z)) 0 0) :
    HasDerivAt (fun r : ℝ => framedNormalizedEndpointMetric Θ M F ((y,r),z)) 0 0 := by
  have h := (hasDerivAt_const (0 : ℝ) (F y).adjoint).clm_comp
    (hzero.clm_comp (hasDerivAt_const (0 : ℝ) (F y)))
  simpa only [Function.comp_def,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,
    add_zero,framedNormalizedEndpointMetric,framedEndpointParameter] using h
end OAI.AnisotropicCalderon.ConnectionError
