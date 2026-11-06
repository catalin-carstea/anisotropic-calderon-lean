import MixedKernelNativeEndpointMetricPullback
import MixedKernelNativeNormalConnectionBound
import MixedKernelNativeQuadraticModel
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator ConformalDepth NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- The ACTUAL native first Hessian block, determined by the exact sphere germ and metric pullback. -/
theorem packet_first_covariant_hessian_formula
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : y ∈ P.centers) (r : ℝ) (hrpos : 0 < r) (hr : r ≤ 4*P.rho)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2)
    (rho : R3 × R3 → ℝ)
    (hRho : ContDiffAt ℝ ∞ rho (packetEndpoint S L P lam y r z,y))
    (hlocal : ∀ᶠ w in 𝓝 z,
      rho (packetEndpoint S L P lam y r w,y) = (⟪w,w⟫_ℝ-1)/2) (U V : R3) :
    let x := packetEndpoint S L P lam y r z
    let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
    let M := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
    let G : R3 → R3 →L[ℝ] R3 := fun w => conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),w))
    r^2*RadiusProfile.coordinateHessian (fun X => rho (X,y))
      (fun A B => coordinateConnectionField (inverseMetricField M) M x A B) x (J U) (J V) =
      ⟪U,V⟫_ℝ-⟪z,coordinateConnectionField (inverseMetricField G) G z U V⟫_ℝ := by
  intro x J M G
  let f := packetEndpoint S L P lam y r
  let u : R3 → ℝ := fun X => rho (X,y)
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  let Theta : R3 × R3 → R3 := fun b => (P.Phi lam b 1).1
  let Frame : R3 → R3 →L[ℝ] R3 := fun Y => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,Y)
  have hTh : ContDiff ℝ ∞ Theta := hTheta.comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ ∞ f :=
    hTh.comp (contDiff_const.prodMk ((Frame y).contDiff.const_smul r))
  have hD : HasFDerivAt f (r • J) z := hasFDerivAt_framedScaledEndpoint_slice Theta Frame hTh y z r
  have hJ := packet_normalizedJacobian_isInvertible S L P lam hlam y hy r
    (by rw [abs_of_pos hrpos];exact hr) z hz
  have hDfInv : (fderiv ℝ f z).IsInvertible := by
    rw [hD.fderiv]
    apply isInvertible_compactChart_endomorphism
    intro A B hab
    apply hJ.injective
    have hh := congrArg (fun Z : R3 => r⁻¹ • Z) hab
    simpa only [ContinuousLinearMap.smul_apply,smul_smul,inv_mul_cancel₀ hrpos.ne',one_smul] using hh
  obtain ⟨hM,_,hSym,hPos,_⟩ := conformalReference_slice_data S.g1 S.g1_admissible L lam
  have hUnit : ∀ Y, IsUnit (M Y) := fun Y => isUnit_of_strictly_positive _ (hPos Y)
  have hu : ContDiffAt ℝ 2 u (f z) :=
    (hRho.of_le (by simp)).comp (f z) (contDiffAt_id.prodMk contDiffAt_const)
  have hGData : ConformalReferenceFramedMetricData S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo := P.native_data.1.1
  rcases hGData with ⟨_,_,_,_,_,hGJoint,_,_⟩
  have hG : ContDiff ℝ ∞ G :=
    hGJoint.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hGInv : (G z).IsInvertible := (packet_nativeMetric_inverse_bound S L P lam hlam y
    (P.centers_room y hy).1.le r (by rw [abs_of_pos hrpos];exact hr) z hz).1
  have hPull := packet_endpoint_pullback_metric_eq S L P lam y r
  have hCov := coordinateHessian_pullback_local M f u hM hf hSym hPos hUnit z U V hDfInv hu
  dsimp only at hCov
  rw [hPull] at hCov
  have hEq : u ∘ f =ᶠ[𝓝 z] normalizedSphereQuadraticModel := hlocal
  have hModel := coordinateHessian_congr_of_eventuallyEq (u ∘ f) normalizedSphereQuadraticModel z
    (fun A B => coordinateConnectionField (inverseMetricField (fun w => r^2 • G w)) (fun w => r^2 • G w) z A B) hEq U V
  rw [coordinateHessian_normalizedSphereQuadraticModel,
    coordinateConnectionField_constant_smul G hG (r^2) (pow_ne_zero 2 hrpos.ne') z U V hGInv] at hModel
  rw [hModel] at hCov
  simp only [hD.fderiv,ContinuousLinearMap.smul_apply] at hCov
  rw [coordinateHessian_smul_vectors] at hCov
  convert hCov.symm using 1 <;> ring

/-- Uniform actual native xx error, with constants chosen before all point/phase parameters. -/
theorem exists_packet_first_covariant_hessian_error_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ P.centers, ∀ r : ℝ, 0 < r → r ≤ 4*P.rho → ∀ z : R3, ‖z‖ = 1 →
      ∀ rho : R3 × R3 → ℝ,
      ContDiffAt ℝ ∞ rho (packetEndpoint S L P lam y r z,y) →
      (∀ᶠ w in 𝓝 z, rho (packetEndpoint S L P lam y r w,y) = (⟪w,w⟫_ℝ-1)/2) →
      ∀ U V : R3,
        let x := packetEndpoint S L P lam y r z
        let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
        let M := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
        |r^2*RadiusProfile.coordinateHessian (fun X => rho (X,y))
          (fun A B => coordinateConnectionField (inverseMetricField M) M x A B) x (J U) (J V)-⟪U,V⟫_ℝ| ≤
          C*r^2*‖U‖*‖V‖ := by
  obtain ⟨C,hC,H⟩ := exists_packet_native_normal_connection_quadratic_bound S L P
  refine ⟨C,hC,?_⟩
  intro lam hlam y hy r hrpos hr z hz rho hRho hlocal U V x J M
  let G : R3 → R3 →L[ℝ] R3 := fun w => conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),w))
  have hFormula := packet_first_covariant_hessian_formula S L P lam hlam y hy r hrpos hr z
    (by simp only [mem_closedBall,dist_zero_right,hz];norm_num) rho hRho hlocal U V
  have hConn : ‖coordinateConnectionField (inverseMetricField G) G z‖ ≤ C*r^2 :=
    H lam hlam y (P.centers_room y hy).1.le r (by rw [abs_of_pos hrpos];exact hr) z (by rw [hz];norm_num)
  have hdiff : r^2*RadiusProfile.coordinateHessian (fun X => rho (X,y))
      (fun A B => coordinateConnectionField (inverseMetricField M) M x A B) x (J U) (J V)-⟪U,V⟫_ℝ =
      -⟪z,coordinateConnectionField (inverseMetricField G) G z U V⟫_ℝ := by
    rw [hFormula]
    ring
  rw [hdiff,abs_neg]
  calc
    |⟪z,coordinateConnectionField (inverseMetricField G) G z U V⟫_ℝ| ≤
        ‖z‖*‖coordinateConnectionField (inverseMetricField G) G z U V‖ := abs_real_inner_le_norm _ _
    _ ≤ C*r^2*‖U‖*‖V‖ := by
      rw [hz,one_mul]
      exact ((coordinateConnectionField (inverseMetricField G) G z U).le_opNorm V).trans
        (mul_le_mul_of_nonneg_right (((coordinateConnectionField (inverseMetricField G) G z).le_opNorm U).trans
          (mul_le_mul_of_nonneg_right hConn (norm_nonneg U))) (norm_nonneg V))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
