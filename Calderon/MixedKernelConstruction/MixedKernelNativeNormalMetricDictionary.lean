import Calderon.MixedKernelConstruction.MixedKernelNativeNormalConnectionBound
import Calderon.MixedKernelConstruction.MixedKernelMetricNormalComparison
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- The genuine normal metric is the exact pullback by the original normalized Jacobian. -/
theorem actual_native_normal_metric_eq_jacobian_pullback
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (y : R3) (r : ℝ) (z : R3) :
    let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
    let x := packetEndpoint S L P lam y r z
    let M := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
    conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),z))=
      J.adjoint.comp ((M x).comp J) := by
  intro J x M
  apply ContinuousLinearMap.ext
  intro U
  apply ext_inner_right ℝ
  intro V
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
  exact framedNormalizedEndpointMetric_inner
    (fun b : R3 × R3 => (P.Phi lam b 1).1) M
    (fun u => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,u)) ((y,r),z) U V

/-- Original zero jets give a true uniform quadratic operator error on the native room. -/
theorem exists_packet_native_normal_metric_operator_error
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, ‖y-P.y0‖ ≤ 4*P.rho → ∀ r : ℝ, |r| ≤ 4*P.rho →
      ∀ z ∈ closedBall (0 : R3) 2,
        ‖conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),z))-
          ContinuousLinearMap.id ℝ R3‖ ≤ D*r^2 := by
  obtain ⟨D,hD,HD⟩ := exists_nativeMetricQuadraticRemainder_compact_bounds S L P 0
  refine ⟨D,hD,?_⟩
  intro lam hlam y hy r hr z hz
  have ha : (lam,((y,r),z))∈conformalReferenceFramedMetricRoom P.y0 (4*P.rho) :=
    ⟨hlam,⟨⟨by simpa only [mem_closedBall,dist_eq_norm] using hy,abs_le.mp hr⟩,hz⟩⟩
  have hA : ‖nativeMetricQuadraticRemainder S L P (lam,((y,r),z))‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_zero] using HD 0 le_rfl _ ha
  rw [native_normal_metric_eq_id_add_radius_sq S L P lam hlam y hy r z hz,
    add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
  exact (mul_le_mul_of_nonneg_left hA (sq_nonneg r)).trans_eq (mul_comm _ _)

/-- The inverse is the ACTUAL native normal inverse, with genuine invertibility discharged. -/
theorem exists_packet_actual_native_normal_inverse_error
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, ‖y-P.y0‖ ≤ 4*P.rho → ∀ r : ℝ, |r| ≤ 4*P.rho →
      ∀ z ∈ closedBall (0 : R3) 2, D*r^2 ≤ 1/2 →
        let G := conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),z))
        ‖ContinuousLinearMap.inverse G‖ ≤ 2 ∧
        ‖ContinuousLinearMap.inverse G-ContinuousLinearMap.id ℝ R3‖ ≤ (2*D)*r^2 := by
  obtain ⟨D,hD,HD⟩ := exists_packet_native_normal_metric_operator_error S L P
  refine ⟨D,hD,?_⟩
  intro lam hlam y hy r hr z hz hSmall G
  have hInv := (packet_nativeMetric_inverse_bound S L P lam hlam y hy r hr z hz).1
  obtain ⟨hNorm,hErr⟩ := inverse_operator_near_identity G (ContinuousLinearMap.inverse G)
    (D*r^2) hSmall (HD lam hlam y hy r hr z hz) hInv.self_apply_inverse
  refine ⟨hNorm,?_⟩
  nlinarith only [hErr]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
