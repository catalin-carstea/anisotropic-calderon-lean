import Calderon.ActualOriginalSourceMetricCarrier
import Calderon.ActualOriginalSourceMetricNativeEquation
import Calderon.MetricPointSourceBoundaryGreen
import Calderon.ActualOriginalSourcePacketChart
import Calderon.ActualOriginalSourcePointSourcePullback
import Calderon.SmoothPositiveMetricCompactGreen
import Calderon.ActualRadiusTwoKernelOffPoleClassicalEquation

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource ConnectionError MetricVolume MetricOperator DirichletFamily Literature SphereHarmonic

private theorem coordinateFluxDivergence_metric_congr_of_eventuallyEq
    (g h : MatrixField) (u : R3 → ℝ) (x : R3) (hNear : g =ᶠ[𝓝 x] h) :
    coordinateFluxDivergence (metricDivergenceFlux g u) x =
      coordinateFluxDivergence (metricDivergenceFlux h u) x := by
  have hFlux : metricDivergenceFlux g u =ᶠ[𝓝 x] metricDivergenceFlux h u := by
    filter_upwards [hNear] with z hz
    have hA : principalCoefficient g z = principalCoefficient h z :=
      congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => Real.sqrt M.det • M⁻¹) hz
    exact congrArg (fun A => matrixOperatorMap A (gradient u z : R3)) hA
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun z => metricDivergenceFlux g u z i) =ᶠ[𝓝 x]
      (fun z => metricDivergenceFlux h u z i) :=
    hFlux.mono (fun z hz => congrArg (fun v : R3 => v i) hz)
  exact congrArg (fun D : R3 →L[ℝ] ℝ => D (NormalCoordinatesFrame.coordinateVector i)) hi.fderiv_eq

theorem exists_actual_original_source_metric_green_kernel
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (lam : ℝ) (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling) :
    ∃ (Fext : R3 → R3) (e : OpenPartialHomeomorph R3 R3) (pole : (radiusTwoOpens : Set R3)),
      ContDiff ℝ ∞ Fext ∧
      (∀ z ∈ closedBall (0 : R3) 2, Fext =ᶠ[𝓝 z]
        (fun w => S.Xi1 (lam • packetEndpoint S L (cover.packet i) lam y r w))) ∧
      (e : R3 → R3) = Fext ∧ e.source = ball (0 : R3) 2 ∧
      Fext 0 = (pole : R3) ∧ (pole : R3) = S.Xi1 (lam • y) ∧
      ContDiffOn ℝ ∞ ((S.G1 pole) ∘ Fext) (ball (0 : R3) 2 \ {0}) ∧
      (∀ z ∈ ball (0 : R3) 2 \ {0}, coordinateFluxDivergence
        (metricDivergenceFlux (originalSourcePacketMetricModel S L (cover.packet i) lam y r)
          ((S.G1 pole) ∘ Fext)) z = 0) ∧
      ∀ psi : 𝓓(radiusTwoOpens,ℝ),
        (∫ z in radiusTwoOpens, S.G1 pole (Fext z) *
          metricCompactTestDensity (originalSourcePacketMetricModel S L (cover.packet i) lam y r) psi z
          ∂(volume : Measure R3)) = psi (0 : R3) := by
  obtain ⟨Fext,e,hF,hNear,he,hs,hInverse,hTarget,hCenter,hJac⟩ :=
    exists_actual_original_source_packet_chart_with_jacobian
      S L cover i lam hlam hlamRoom y hy r hrpos hrceil
  have h0 : (0 : R3) ∈ e.source := by rw [hs]; norm_num
  have h0Target : Fext 0 ∈ (radiusTwoOpens : Set R3) := by
    have h := hTarget (e.map_source h0)
    simpa only [he] using h
  let pole : (radiusTwoOpens : Set R3) := ⟨Fext 0,h0Target⟩
  let g := originalSourcePacketMetricModel S L (cover.packet i) lam y r
  let T : Set R3 := (radiusTwoOpens : Set R3) \ {(pole : R3)}
  have hT : IsOpen T := radiusTwoOpens.isOpen.sdiff isClosed_singleton
  have hMap : ∀ z ∈ ball (0 : R3) 2 \ {0}, Fext z ∈ T := by
    intro z hz
    have hzSource : z ∈ e.source := by rw [hs]; exact hz.1
    have hRoom : Fext z ∈ (radiusTwoOpens : Set R3) := by
      have h := hTarget (e.map_source hzSource)
      simpa only [he] using h
    refine ⟨hRoom,?_⟩
    intro hp
    have hEq : Fext z = Fext 0 := mem_singleton_iff.mp hp
    have hz0 : z = 0 := e.injOn hzSource h0 (by simpa only [he] using hEq)
    exact hz.2 (mem_singleton_iff.mpr hz0)
  have hMetricNear : ∀ z ∈ ball (0 : R3) 2, pullbackMetric S.original1 Fext =ᶠ[𝓝 z] g := by
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact pullbackMetric_original_source_extension_eq_model
      S L cover i lam hlam hlamRoom y hy r hrpos hrceil Fext hNear w (ball_subset_closedBall hw)
  have hRow := radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
    S.hreg S.hcalc S.original1 S.original1_admissible S.K1 S.G1 S.kernel1.1 pole
  have hSmooth : ContDiffOn ℝ ∞ ((S.G1 pole) ∘ Fext) (ball (0 : R3) 2 \ {0}) :=
    hRow.1.comp hF.contDiffOn hMap
  refine ⟨Fext,e,pole,hF,hNear,he,hs,rfl,hCenter,hSmooth,?_,?_⟩
  · intro z hz
    have hOriginal : coordinateFluxDivergence (metricDivergenceFlux S.original1 (S.G1 pole)) (Fext z) = 0 := by
      have h := hRow.2 (Fext z) (hMap z hz)
      rw [nativeMetricDifferential_eq_neg_coordinateFluxDivergence] at h
      exact neg_eq_zero.mp h
    have hCov := coordinateFluxDivergence_pullbackMetric_of_contDiffOn
      S.original1 S.original1_admissible.smooth S.original1_admissible.posDef Fext
      (S.G1 pole) (ball (0 : R3) 2) T isOpen_ball hT hF.contDiffOn hRow.1
      z hz.1 (hMap z hz) (hJac z hz.1)
    have hZero : coordinateFluxDivergence
        (metricDivergenceFlux (pullbackMetric S.original1 Fext) ((S.G1 pole) ∘ Fext)) z = 0 := by
      rw [hOriginal,mul_zero] at hCov
      exact hCov
    exact (coordinateFluxDivergence_metric_congr_of_eventuallyEq
      (pullbackMetric S.original1 Fext) g ((S.G1 pole) ∘ Fext) z (hMetricNear z hz.1)).symm.trans hZero
  · intro psi
    have hSource := original_first_kernel_pointSource_pullback
      S Fext hF e he hs hInverse hTarget pole rfl hJac psi
    have hIntegral : (∫ z in radiusTwoOpens, S.G1 pole (Fext z) * metricCompactTestDensity g psi z ∂volume) =
        ∫ z in ball (0 : R3) 2, S.G1 pole (Fext z) *
          (-coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric S.original1 Fext)
            (psi : R3 → ℝ)) z) ∂volume := by
      apply setIntegral_congr_fun isOpen_ball.measurableSet
      intro z hz
      dsimp only [metricCompactTestDensity]
      exact congrArg (fun t : ℝ => S.G1 pole (Fext z) * (-t))
        (coordinateFluxDivergence_metric_congr_of_eventuallyEq
          (pullbackMetric S.original1 Fext) g (psi : R3 → ℝ) z (hMetricNear z hz)).symm
    exact hIntegral.trans hSource

theorem exists_actual_original_source_native_harmonic_green
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (lam : ℝ) (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling) :
    ∃ (Fext : R3 → R3) (pole : (radiusTwoOpens : Set R3)), ContDiff ℝ ∞ Fext ∧
      (∀ z ∈ closedBall (0 : R3) 2, Fext =ᶠ[𝓝 z]
        (fun w => S.Xi1 (lam • packetEndpoint S L (cover.packet i) lam y r w))) ∧
      Fext 0 = (pole : R3) ∧ (pole : R3) = S.Xi1 (lam • y) ∧
      ∀ v : SmoothData,
        (∀ z ∈ ball (0 : R3) 1, coordinateFluxDivergence (fun x => matrixOperatorMap
          (DirichletFamily.DriftBootstrap.referencePhysicalNormalizedPrincipalCoefficient
            S.g1 L (cover.packet i).Phi (cover.packet i).H (lam,(y,r)) x)
          (gradient v.1 x : R3)) z = 0) →
        (∫ theta : UnitSphere,
          ⟪theta.val,metricWronskianFlux
            (originalSourcePacketMetricModel S L (cover.packet i) lam y r)
            v.1 ((S.G1 pole) ∘ Fext) theta.val⟫_ℝ ∂SphereHarmonic.surfaceMeasure) = v.1 (0 : R3) := by
  obtain ⟨Fext,e,pole,hF,hNear,_,_,hPole,hCenter,hSmooth,hPDE,hPoint⟩ :=
    exists_actual_original_source_metric_green_kernel
      S L cover i lam hlam hlamRoom y hy r hrpos hrceil
  have hMetric := originalSourcePacketMetricModel_smooth_positive S L (cover.packet i) lam y r
  refine ⟨Fext,pole,hF,hNear,hPole,hCenter,?_⟩
  intro v hNative
  apply metric_pointSource_unitSphere_green
    (originalSourcePacketMetricModel S L (cover.packet i) lam y r)
    hMetric.1 hMetric.2 ((S.G1 pole) ∘ Fext) hSmooth hPDE
  · intro psi
    exact hPoint psi
  · exact originalSourcePacketMetricModel_harmonic_of_native_normalized
      S L (cover.packet i) lam hlam y r hrpos v hNative

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
