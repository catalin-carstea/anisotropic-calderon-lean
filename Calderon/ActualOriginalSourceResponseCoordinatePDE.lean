import Calderon.ActualGlobalNativeDensityPairedReproduction
import Calderon.ActualSourceChartHarmonicColumns
import Calderon.LocalMetricPullbackDivergence
import Calderon.RadiusTwoSmoothSourceClassicalEquation
import Calderon.ActualNormalizedSecondUCPDictionary

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError

theorem coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
    (g h : MatrixField) (u : R3 → ℝ) (x : R3) (hMetric : g =ᶠ[𝓝 x] h) :
    coordinateFluxDivergence (metricDivergenceFlux g u) x =
      coordinateFluxDivergence (metricDivergenceFlux h u) x := by
  have hFlux : metricDivergenceFlux g u =ᶠ[𝓝 x] metricDivergenceFlux h u := by
    filter_upwards [hMetric] with y hy
    change matrixOperatorMap (Real.sqrt (g y).det • (g y)⁻¹) (gradient u y) =
      matrixOperatorMap (Real.sqrt (h y).det • (h y)⁻¹) (gradient u y)
    rw [hy]
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y => metricDivergenceFlux g u y i) =ᶠ[𝓝 x]
      (fun y => metricDivergenceFlux h u y i) :=
    hFlux.mono (fun y hy => congrArg (fun v : R3 => v i) hy)
  exact congrArg (fun A : R3 →L[ℝ] ℝ => A (NormalCoordinatesFrame.coordinateVector i))
    hi.fderiv_eq

theorem coordinateFluxDivergence_originalSourceResponse_pullback_eq_zero
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g a : MatrixField) (hg : IsAdmissibleMetric g)
    (U : Set R3) (hU : IsOpen U) (Xi : R3 → R3) (hXi : ContDiffOn ℝ ∞ Xi U)
    (hRoom : ∀ z ∈ U, Xi z ∈ (radiusTwoOpens : Set R3))
    (hJac : ∀ z ∈ U, IsUnit (coordinateJacobianMatrix Xi z).det)
    (hCarrier : EqOn a (pullbackMetric g Xi) U)
    (s : 𝓓(fixedExteriorSourceOpens, ℝ)) (x : R3) (hx : x ∈ U)
    (hSource : Xi x ∉ tsupport s) :
    coordinateFluxDivergence (metricDivergenceFlux a
      (fun z => radiusTwoSmoothSourceResponse hreg hcalc g hg s (Xi z))) x = 0 := by
  let u := radiusTwoSmoothSourceResponse hreg hcalc g hg s
  have hOriginal : coordinateFluxDivergence (metricDivergenceFlux g u) (Xi x) = 0 := by
    have hNative := nativeMetricDifferential_radiusTwoSmoothSourceResponse
      hreg hcalc g hg s (Xi x) (hRoom x hx)
    rw [nativeMetricDifferential_eq_neg_coordinateFluxDivergence] at hNative
    have hs : s (Xi x) = 0 := image_eq_zero_of_notMem_tsupport hSource
    rw [hs] at hNative
    exact neg_eq_zero.mp hNative
  have hCov := coordinateFluxDivergence_pullbackMetric_of_contDiffOn
    g hg.smooth hg.posDef Xi u U (radiusTwoOpens : Set R3)
    hU radiusTwoOpens.isOpen hXi
    (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg s).2.1
    x hx (hRoom x hx) (hJac x hx)
  have hMetric : a =ᶠ[𝓝 x] pullbackMetric g Xi := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hCarrier hz
  exact (coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
    a (pullbackMetric g Xi) (u ∘ Xi) x hMetric).trans
      (hCov.trans (by rw [hOriginal, mul_zero]))

theorem coordinateFluxDivergence_dilated_original_first_sourceResponse_eq_zero
    (S : KnownSideSourceData) (lam : ℝ) (s : 𝓓(fixedExteriorSourceOpens, ℝ))
    (x : R3) (hx : lam • x ∈ S.coordinateRoom)
    (hSource : S.Xi1 (lam • x) ∉ tsupport s) :
    coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z))
      (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible s (S.Xi1 (lam • z)))) x = 0 := by
  let u : R3 → ℝ := fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
    S.original1_admissible s (S.Xi1 z)
  have hu : ContDiffOn ℝ ∞ u S.coordinateRoom :=
    (radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original1
      S.original1_admissible s).2.1.comp S.Xi1_smooth S.Xi1_room
  have hPDE := coordinateFluxDivergence_originalSourceResponse_pullback_eq_zero
    S.hreg S.hcalc S.original1 S.g1 S.original1_admissible
    S.coordinateRoom S.coordinateRoom_open S.Xi1 S.Xi1_smooth S.Xi1_room S.Xi1_jacobian
    S.carrier1 s (lam • x) hx hSource
  have hDil := coordinateFluxDivergence_metricDivergenceFlux_dilation_of_contDiffOn
    S.g1 S.g1_admissible lam S.coordinateRoom S.coordinateRoom_open u hu x hx
  exact hDil.trans (by rw [hPDE, mul_zero])

theorem coordinateFluxDivergence_dilated_original_second_sourceResponse_eq_zero
    (S : KnownSideSourceData) (lam : ℝ) (s : 𝓓(fixedExteriorSourceOpens, ℝ))
    (x : R3) (hx : lam • x ∈ S.coordinateRoom)
    (hSource : S.Xi2 (lam • x) ∉ tsupport s) :
    coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g2 (lam • z))
      (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
        S.original2_admissible s (S.Xi2 (lam • z)))) x = 0 := by
  let u : R3 → ℝ := fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
    S.original2_admissible s (S.Xi2 z)
  have hu : ContDiffOn ℝ ∞ u S.coordinateRoom :=
    (radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original2
      S.original2_admissible s).2.1.comp S.Xi2_smooth S.Xi2_room
  have hPDE := coordinateFluxDivergence_originalSourceResponse_pullback_eq_zero
    S.hreg S.hcalc S.original2 S.g2 S.original2_admissible
    S.coordinateRoom S.coordinateRoom_open S.Xi2 S.Xi2_smooth S.Xi2_room S.Xi2_jacobian
    S.carrier2 s (lam • x) hx hSource
  have hDil := coordinateFluxDivergence_metricDivergenceFlux_dilation_of_contDiffOn
    S.g2 S.g2_admissible lam S.coordinateRoom S.coordinateRoom_open u hu x hx
  exact hDil.trans (by rw [hPDE, mul_zero])

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
