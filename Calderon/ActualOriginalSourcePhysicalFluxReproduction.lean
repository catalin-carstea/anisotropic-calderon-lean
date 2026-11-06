import Calderon.ActualOriginalSourceMetricGreenKernel
import Calderon.ActualOriginalSourcePrincipalScaling
import Calderon.ActualPacketPhysicalHarmonicNativeEquation
import Calderon.MetricWronskianPullbackScaling
import Calderon.ActualMixedKernelOriginalReferenceGerms

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ConnectionError MetricVolume MetricOperator DirichletFamily.DriftBootstrap
  ExteriorSource SphereHarmonic ConformalDepth ReferenceWeightedApproximation

theorem nativeMixedKernelWronskianFlux_eq_value_on_original_known_side
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers)
    (hrceil : referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (hKnown : lam • y ∈ S.W)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (hGerm : ∀ theta ∈ sphere (0 : R3) 1, Gext =ᶠ[𝓝 (packetEndpoint S L (cover.packet i)
      lam y (referenceRadius delta Rstar p L y) theta,y)] K.kernel)
    (u : SmoothData)
    (hphysical : ∀ z ∈ ball (0 : R3) 1, coordinateFluxDivergence
      (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
      (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) :
    nativeMixedKernelWronskianFlux S L (cover.packet i) lam Gext u.1
      y (referenceRadius delta Rstar p L y) y = u.1 y := by
  let P := cover.packet i
  let r := referenceRadius delta Rstar p L y
  let X : R3 → R3 := packetEndpoint S L P lam y r
  let g := originalSourcePacketMetricModel S L P lam y r
  let gq : MatrixField := fun x => S.g1 (lam • x)
  let E : SmoothData := mixedKernelPhysicalSlice Gext hG y
  let v : SmoothData := referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
    P.native_data.1.1.1 lam y r u
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩
  have hrpos : 0 < r := referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hc : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy.2).1.le
  have hr : |r| ≤ 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact (hrceil.trans (cover.radius_room i)).le
  have hTheta : ContDiff ℝ ∞ (fun t : ℝ × (R3 × R3) => (P.Phi t.1 t.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hv : v.1 = u.1 ∘ X := rfl
  have hE : ContDiff ℝ ∞ (E.1 ∘ X) := E.2.comp hX
  have hNative := actual_packet_native_normalized_harmonic_of_physical
    S L cover i lam ⟨hlam.le,hlamRoom⟩ y hy.2 r hrpos hrceil u hphysical
  obtain ⟨Fext,pole,hF,hFNear,hPole,hCenter,hGreen⟩ :=
    exists_actual_original_source_native_harmonic_green
      S L cover i lam hlam hlamRoom y hy.2 r hrpos hrceil
  have hBoundary := original_reference_kernel_eventuallyEq_reciprocal_same_mixed_datum
    S L lam delta Rstar bound separation p cover K hlam i y hy hKnown Gext hGerm Fext
    (fun theta ht => hFNear theta (closedBall_subset_closedBall (by norm_num)
      (sphere_subset_closedBall ht))) pole hCenter
  have hFlux (theta : UnitSphere) : metricWronskianFlux g v.1 ((S.G1 pole) ∘ Fext) theta.val =
      signedPiolaFlux X (metricWronskianFlux gq u.1 E.1) theta.val := by
    have ht2 : theta.val ∈ closedBall (0 : R3) 2 :=
      closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall theta.property)
    have hCoeff := original_source_model_principalCoefficient_eq_lambda_pullback
      S L cover i lam hlam hlamRoom y hy.2 r hrpos hrceil theta.val ht2
    have hdet : 0 < (coordinateJacobianMatrix X theta.val).det :=
      coordinateJacobianMatrix_referencePhysicalEndpoint_det_pos
        S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
        lam hq y hc r hr hrpos theta.val ht2
    calc
      metricWronskianFlux g v.1 ((S.G1 pole) ∘ Fext) theta.val =
          metricWronskianFlux g v.1 (fun z => lam⁻¹*(E.1 ∘ X) z) theta.val :=
        metricWronskianFlux_congr_right_of_eventuallyEq g v.1 _ _ theta.val
          (hBoundary theta.val theta.property).symm
      _ = metricWronskianFlux (pullbackMetric gq X) v.1 (E.1 ∘ X) theta.val :=
        metricWronskianFlux_scaled_coefficient_reciprocal_kernel g (pullbackMetric gq X)
          lam hlam.ne' v.1 (E.1 ∘ X) theta.val (hE.differentiable (by simp) _) hCoeff
      _ = signedPiolaFlux X (metricWronskianFlux gq u.1 E.1) theta.val := by
        rw [hv]
        exact metricWronskianFlux_pullbackMetric_eq_signedPiolaFlux
          gq X u.1 E.1 hX u.2 E.2 theta.val hdet
  have hIntegral : (∫ theta : UnitSphere,
      ⟪theta.val,metricWronskianFlux g v.1 ((S.G1 pole) ∘ Fext) theta.val⟫_ℝ ∂surfaceMeasure) =
      nativeMixedKernelWronskianFlux S L P lam Gext u.1 y r y := by
    unfold nativeMixedKernelWronskianFlux
    apply integral_congr_ae
    apply ae_of_all
    intro theta
    exact congrArg (fun w : R3 => ⟪theta.val,w⟫_ℝ) (hFlux theta)
  have hv0 : v.1 (0 : R3) = u.1 y := by
    change u.1 (packetEndpoint S L P lam y r 0) = u.1 y
    rw [packetEndpoint_zero_eq_center S L P lam hq y hy.2 r]
  exact hIntegral.symm.trans ((hGreen v hNative).trans hv0)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
