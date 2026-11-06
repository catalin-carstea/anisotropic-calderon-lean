import MixedKernelActualConnectionPullback
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric ConnectionError MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace

/-- The SAME actual physical endpoint has metric pullback EXACTLY r squared times its native normal metric. -/
theorem packet_endpoint_pullback_metric_eq
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) (lam : ℝ) (y : R3) (r : ℝ) :
    let M := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
    let f := packetEndpoint S L P lam y r
    pullbackCoordinateMetric M f =
      fun w : R3 => r^2 • conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),w)) := by
  intro M f
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  let Theta : R3 × R3 → R3 := fun b => (P.Phi lam b 1).1
  let Frame : R3 → R3 →L[ℝ] R3 := fun u => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,u)
  have hD (w : R3) : HasFDerivAt f
      (r • referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),w))) w :=
    hasFDerivAt_framedScaledEndpoint_slice Theta Frame
      (hTheta.comp (contDiff_const.prodMk contDiff_id)) y w r
  funext w
  apply ContinuousLinearMap.ext
  intro U
  apply ext_inner_right ℝ
  intro V
  change ⟪(fderiv ℝ f w).adjoint (M (f w) (fderiv ℝ f w U)),V⟫_ℝ =
    ⟪(r^2 • conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),w))) U,V⟫_ℝ
  rw [ContinuousLinearMap.adjoint_inner_left,(hD w).fderiv]
  simp only [ContinuousLinearMap.smul_apply,map_smul,real_inner_smul_left,real_inner_smul_right]
  have hMetric := framedNormalizedEndpointMetric_inner Theta M Frame ((y,r),w) U V
  have hMetric' :
      ⟪conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),w)) U,V⟫_ℝ =
      ⟪M (f w) (referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),w)) U),
        referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),w)) V⟫_ℝ := hMetric
  rw [hMetric']
  ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
