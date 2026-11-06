import Calderon.GeodesicEndpoint
import Calderon.MetricOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProduct
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def scaledEndpoint (Θ : E × E → E) (p : (E × ℝ) × E) : E :=
  Θ (p.1.1,p.1.2 • p.2)

def normalizedEndpointDerivative (Θ : E × E → E) (p : (E × ℝ) × E) : E →L[ℝ] E :=
  (fderiv ℝ Θ (p.1.1,p.1.2 • p.2)).comp (ContinuousLinearMap.inr ℝ E E)

def normalizedEndpointMetric (Θ : E × E → E) (M : E → E →L[ℝ] E)
    (p : (E × ℝ) × E) : E →L[ℝ] E :=
  (normalizedEndpointDerivative Θ p).adjoint.comp
    ((M (scaledEndpoint Θ p)).comp (normalizedEndpointDerivative Θ p))

omit [CompleteSpace E] in
theorem contDiff_scaledEndpoint (Θ : E × E → E) (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ (scaledEndpoint Θ) :=
  hΘ.comp ((contDiff_fst.fst).prodMk ((contDiff_fst.snd).smul contDiff_snd))

omit [CompleteSpace E] in
theorem contDiff_normalizedEndpointDerivative (Θ : E × E → E)
    (hΘ : ContDiff ℝ ∞ Θ) : ContDiff ℝ ∞ (normalizedEndpointDerivative Θ) :=
  ((hΘ.fderiv_right (by simp)).comp
    ((contDiff_fst.fst).prodMk ((contDiff_fst.snd).smul contDiff_snd))).clm_comp
      contDiff_const

theorem contDiff_normalizedEndpointMetric (Θ : E × E → E)
    (M : E → E →L[ℝ] E) (hΘ : ContDiff ℝ ∞ Θ) (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (normalizedEndpointMetric Θ M) := by
  have hJ := contDiff_normalizedEndpointDerivative Θ hΘ
  have hA : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => L.adjoint) :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E)).contDiff
  exact (hA.comp hJ).clm_comp
    ((hM.comp (contDiff_scaledEndpoint Θ hΘ)).clm_comp hJ)

theorem normalizedEndpointMetric_inner (Θ : E × E → E) (M : E → E →L[ℝ] E)
    (p : (E × ℝ) × E) (u v : E) :
    inner ℝ (normalizedEndpointMetric Θ M p u) v =
      inner ℝ (M (scaledEndpoint Θ p) (normalizedEndpointDerivative Θ p u))
        (normalizedEndpointDerivative Θ p v) := by
  change inner ℝ ((normalizedEndpointDerivative Θ p).adjoint
    (M (scaledEndpoint Θ p) (normalizedEndpointDerivative Θ p u))) v = _
  exact ContinuousLinearMap.adjoint_inner_left (normalizedEndpointDerivative Θ p) v
    (M (scaledEndpoint Θ p) (normalizedEndpointDerivative Θ p u))

omit [CompleteSpace E] in
theorem scaledEndpoint_zero (Θ : E × E → E) (y z : E) (hzero : Θ (y,0) = y) :
    scaledEndpoint Θ ((y,0),z) = y := by simp [scaledEndpoint,hzero]

omit [CompleteSpace E] in
theorem normalizedEndpointDerivative_zero (Θ : E × E → E) (y z : E)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0)) :
    normalizedEndpointDerivative Θ ((y,0),z) = ContinuousLinearMap.id ℝ E := by
  simp only [normalizedEndpointDerivative,zero_smul,hD.fderiv]
  apply ContinuousLinearMap.ext
  intro u
  change (0 : E) + u = u
  exact zero_add u

theorem normalizedEndpointMetric_zero (Θ : E × E → E) (M : E → E →L[ℝ] E)
    (y z : E) (hzero : Θ (y,0) = y)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0)) :
    normalizedEndpointMetric Θ M ((y,0),z) = M y := by
  simp [normalizedEndpointMetric,normalizedEndpointDerivative_zero Θ y z hD,
    scaledEndpoint_zero Θ y z hzero,ContinuousLinearMap.adjoint_id]

omit [CompleteSpace E] in
theorem hasFDerivAt_scaledEndpoint_slice (Θ : E × E → E) (hΘ : ContDiff ℝ ∞ Θ)
    (y z : E) (r : ℝ) :
    HasFDerivAt (fun w => Θ (y,r • w))
      (r • normalizedEndpointDerivative Θ ((y,r),z)) z := by
  have hi : HasFDerivAt (fun w : E => (y,r • w))
      (r • ContinuousLinearMap.inr ℝ E E) z := by
    have hc : HasFDerivAt (fun _ : E => y) (0 : E →L[ℝ] E) z := hasFDerivAt_const y z
    have hid : HasFDerivAt (fun w : E => w) (ContinuousLinearMap.id ℝ E) z := hasFDerivAt_id z
    have hs : HasFDerivAt (fun w : E => r • w) (r • ContinuousLinearMap.id ℝ E) z :=
      hid.const_smul r
    convert hc.prodMk hs using 1
    apply ContinuousLinearMap.ext
    intro u
    simp
  convert ((hΘ.differentiable (by simp) (y,r • z)).hasFDerivAt).comp z hi using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro u
    simp [normalizedEndpointDerivative]

theorem scaledEndpoint_pullback_inner (Θ : E × E → E) (M : E → E →L[ℝ] E)
    (hΘ : ContDiff ℝ ∞ Θ) (y z u v : E) (r : ℝ) :
    inner ℝ (M (Θ (y,r • z)) (fderiv ℝ (fun w => Θ (y,r • w)) z u))
      (fderiv ℝ (fun w => Θ (y,r • w)) z v) =
      r^2 * inner ℝ (normalizedEndpointMetric Θ M ((y,r),z) u) v := by
  rw [(hasFDerivAt_scaledEndpoint_slice Θ hΘ y z r).fderiv,
    normalizedEndpointMetric_inner]
  simp [scaledEndpoint,real_inner_smul_left,real_inner_smul_right,pow_two,mul_assoc]

end OAI.AnisotropicCalderon.ConnectionError

namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError
theorem exists_smooth_metric_geodesic_endpoint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (y0 : R3) :
    ∃ (Φ : (R3 × R3) → ℝ → R3 × R3) (A : Set (R3 × R3)),
      IsOpen A ∧ (y0,0) ∈ A ∧
      ContDiff ℝ ∞ (fun p : (R3 × R3) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧
      (∀ y, (y,0) ∈ A → ∀ t, Φ (y,0) t = (y,0)) ∧
      (∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Φ z) (geodesicPhaseField
          (inverseMetricField (metricOperatorField g)) (metricOperatorField g) (Φ z t)) t) ∧
      ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      ∀ y, (y,0) ∈ A → HasFDerivAt (fun z => (Φ z 1).1)
        (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0) :=
  exists_smooth_coordinate_spray_endpoint _ _
    (contDiff_inverseMetricField _ (contDiff_metricOperatorField g hg)
      (isUnit_metricOperatorField g hg)) (contDiff_metricOperatorField g hg) y0
end OAI.AnisotropicCalderon.MetricOperator
