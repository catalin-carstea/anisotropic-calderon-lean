import Calderon.ActualOriginalChartSourceData
import Calderon.ActualCommonLinearMetricNormalization
import Calderon.ActualOneSidedLinearNormalization

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Distributions Matrix.Norms.Elementwise Matrix
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError
  NativeSourceChartCalculus NormalCoordinatesFrame

theorem exists_known_side_source_data_of_unnormalized_original_charts
    (original1 original2 : MatrixField)
    (hOriginal1 : IsAdmissibleMetric original1) (hOriginal2 : IsAdmissibleMetric original2)
    (K1 K2 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G1 G2 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hKernel1 : IsRadiusTwoSeparatelySmoothInverseSourceKernel original1 hOriginal1 K1 G1)
    (hKernel2 : IsRadiusTwoSeparatelySmoothInverseSourceKernel original2 hOriginal2 K2 G2)
    (U : Set R3) (hU : IsOpen U) (h0 : (0 : R3) ∈ U)
    (Xi1 Xi2 : R3 → R3)
    (hSmooth1 : ContDiffOn ℝ ∞ Xi1 U) (hSmooth2 : ContDiffOn ℝ ∞ Xi2 U)
    (hInjective1 : Set.InjOn Xi1 U) (hInjective2 : Set.InjOn Xi2 U)
    (hJac1 : ∀ x ∈ U, IsUnit (coordinateJacobianMatrix Xi1 x).det)
    (hJac2 : ∀ x ∈ U, IsUnit (coordinateJacobianMatrix Xi2 x).det)
    (hRange1 : ∀ x ∈ U, Xi1 x ∈ (radiusTwoOpens : Set R3))
    (hRange2 : ∀ x ∈ U, Xi2 x ∈ (radiusTwoOpens : Set R3))
    (hHarmonic1 : ∀ i : Fin 3, ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric original1 Xi1) (fun z => z i)) x = 0)
    (hHarmonic2 : ∀ i : Fin 3, ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric original2 Xi2) (fun z => z i)) x = 0)
    (W : Set R3) (hW : IsOpen W) (hWU : W ⊆ U)
    (hMetrics : EqOn (pullbackMetric original1 Xi1) (pullbackMetric original2 Xi2) W)
    (hKernels : ∀ x : R3, ∀ hx : x ∈ W, ∀ y : R3, ∀ hy : y ∈ W, x ≠ y →
      G1 ⟨Xi1 y,hRange1 y (hWU hy)⟩ (Xi1 x) = G2 ⟨Xi2 y,hRange2 y (hWU hy)⟩ (Xi2 x))
    (sep : R3 → ℝ) (hSep : ContDiffOn ℝ ∞ sep U) (hZero : sep 0 = 0)
    (hNormal : ∀ v : R3, fderiv ℝ sep 0 v = v 2)
    (hSide : ∃ a : ℝ, 0 < a ∧ ball (0 : R3) a ⊆ U ∧
      {z ∈ ball (0 : R3) a | sep z < 0} ⊆ W) :
    ∃ (A : R3 ≃L[ℝ] R3) (c : ℝ), 0 < c ∧ (∀ v : R3, (A v) 2 = c * v 2) ∧
    ∃ S : KnownSideSourceData,
      S.hreg = fixedDirichletRegularity ∧ S.hcalc = fixedSobolevCalculus ∧
      S.original1 = original1 ∧ S.original2 = original2 ∧
      S.K1 = K1 ∧ S.K2 = K2 ∧ S.G1 = G1 ∧ S.G2 = G2 ∧
      S.Xi1 = Xi1 ∘ A ∧ S.Xi2 = Xi2 ∘ A ∧
      S.separating_function = (fun x => c⁻¹ * sep (A x)) ∧
      S.coordinateRoom ⊆ A ⁻¹' U ∧ S.W = (A ⁻¹' W) ∩ S.coordinateRoom ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        (∀ x ∈ W,
          radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original1 hOriginal1 s (Xi1 x) =
          radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original2 hOriginal2 s (Xi2 x)) →
        ∀ x ∈ S.W,
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x) := by
  have hPB1 := contDiffOn_native_source_chart_pullbackMetric original1 hOriginal1 Xi1 U hU hSmooth1
  have hPB2 := contDiffOn_native_source_chart_pullbackMetric original2 hOriginal2 Xi2 U hU hSmooth2
  have hEntry1 : ∀ i j : Fin 3, ContDiffOn ℝ ∞ (fun x => pullbackMetric original1 Xi1 x i j) U :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hPB1 i) j
  have hEntry2 : ∀ i j : Fin 3, ContDiffOn ℝ ∞ (fun x => pullbackMetric original2 Xi2 x i j) U :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hPB2 i) j
  have hPos1 : ∀ x ∈ U, (pullbackMetric original1 Xi1 x).PosDef := by
    intro x hx
    exact pullbackMetric_posDef_of_injective_fderiv original1 hOriginal1 Xi1 x
      (injective_fderiv_of_unit_coordinate_jacobian Xi1 x (hJac1 x hx))
  have hPos2 : ∀ x ∈ U, (pullbackMetric original2 Xi2 x).PosDef := by
    intro x hx
    exact pullbackMetric_posDef_of_injective_fderiv original2 hOriginal2 Xi2 x
      (injective_fderiv_of_unit_coordinate_jacobian Xi2 x (hJac2 x hx))
  obtain ⟨a1,ha1,_,hBallU1,c1,hc1,hc1Eq⟩ :=
    exists_admissible_metric_eq_on_local_closed_ball (pullbackMetric original1 Xi1) U hU h0 hEntry1 hPos1
  obtain ⟨a2,ha2,_,hBallU2,c2,hc2,hc2Eq⟩ :=
    exists_admissible_metric_eq_on_local_closed_ball (pullbackMetric original2 Xi2) U hU h0 hEntry2 hPos2
  let b := min a1 a2
  let room := ball (0 : R3) b
  have hb : 0 < b := lt_min ha1 ha2
  have hRoom : IsOpen room := isOpen_ball
  have h0Room : (0 : R3) ∈ room := mem_ball_self hb
  have hRoom1 : room ⊆ closedBall (0 : R3) a1 :=
    (ball_subset_ball (min_le_left a1 a2)).trans ball_subset_closedBall
  have hRoom2 : room ⊆ closedBall (0 : R3) a2 :=
    (ball_subset_ball (min_le_right a1 a2)).trans ball_subset_closedBall
  have hRoomU : room ⊆ U := hRoom1.trans hBallU1
  have hC1 : EqOn c1 (pullbackMetric original1 Xi1) room := fun _ hx => hc1Eq (hRoom1 hx)
  have hC2 : EqOn c2 (pullbackMetric original2 Xi2) room := fun _ hx => hc2Eq (hRoom2 hx)
  have hColumns1 : ∀ i : Fin 3, ∀ x ∈ room,
      coordinateFluxDivergence (metricDivergenceFlux c1 (fun z => z i)) x = 0 := by
    intro i x hx
    have hNear : c1 =ᶠ[𝓝 x] pullbackMetric original1 Xi1 := by
      filter_upwards [hRoom.mem_nhds hx] with y hy
      exact hC1 hy
    exact (coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
      c1 (pullbackMetric original1 Xi1) (fun z => z i) x hNear).trans (hHarmonic1 i x (hRoomU hx))
  have hColumns2 : ∀ i : Fin 3, ∀ x ∈ room,
      coordinateFluxDivergence (metricDivergenceFlux c2 (fun z => z i)) x = 0 := by
    intro i x hx
    have hNear : c2 =ᶠ[𝓝 x] pullbackMetric original2 Xi2 := by
      filter_upwards [hRoom.mem_nhds hx] with y hy
      exact hC2 hy
    exact (coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
      c2 (pullbackMetric original2 Xi2) (fun z => z i) x hNear).trans (hHarmonic2 i x (hRoomU hx))
  obtain ⟨A,c,hc,hNorm,hThird⟩ :=
    exists_metric_normalizing_linear_equiv_preserving_third_coordinate c1 hc1
  let newRoom := A ⁻¹' room
  let newW := A ⁻¹' (W ∩ room)
  have hNewRoom : IsOpen newRoom := hRoom.preimage A.continuous
  have h0NewRoom : (0 : R3) ∈ newRoom := by
    change A (0 : R3) ∈ room
    simpa only [map_zero] using h0Room
  have hNewW : IsOpen newW := (hW.inter hRoom).preimage A.continuous
  have hNewWRoom : newW ⊆ newRoom := fun _ hx => hx.2
  have hXi1New : ContDiffOn ℝ ∞ (Xi1 ∘ A) newRoom :=
    (hSmooth1.mono hRoomU).comp A.contDiff.contDiffOn (fun _ hx => hx)
  have hXi2New : ContDiffOn ℝ ∞ (Xi2 ∘ A) newRoom :=
    (hSmooth2.mono hRoomU).comp A.contDiff.contDiffOn (fun _ hx => hx)
  have hInj1New : Set.InjOn (Xi1 ∘ A) newRoom := by
    intro x hx y hy hxy
    exact A.injective (hInjective1 (hRoomU hx) (hRoomU hy) hxy)
  have hInj2New : Set.InjOn (Xi2 ∘ A) newRoom := by
    intro x hx y hy hxy
    exact A.injective (hInjective2 (hRoomU hx) (hRoomU hy) hxy)
  have hJac1New : ∀ x ∈ newRoom, IsUnit (coordinateJacobianMatrix (Xi1 ∘ A) x).det := by
    intro x hx
    have hDX := (hSmooth1.contDiffAt (hU.mem_nhds (hRoomU hx))).differentiableAt (by simp)
    have hChain := (hDX.hasFDerivAt.comp x A.hasFDerivAt).fderiv
    have hJac : coordinateJacobianMatrix (Xi1 ∘ A) x =
        coordinateJacobianMatrix Xi1 (A x) * coordinateJacobianMatrix A x := by
      simp only [coordinateJacobianMatrix_eq_operatorMatrixMap,hChain,A.fderiv,operatorMatrixMap_comp]
    rw [hJac,Matrix.det_mul]
    exact (hJac1 (A x) (hRoomU hx)).mul (isUnit_det_coordinateJacobianMatrix_continuousLinearEquiv A x)
  have hJac2New : ∀ x ∈ newRoom, IsUnit (coordinateJacobianMatrix (Xi2 ∘ A) x).det := by
    intro x hx
    have hDX := (hSmooth2.contDiffAt (hU.mem_nhds (hRoomU hx))).differentiableAt (by simp)
    have hChain := (hDX.hasFDerivAt.comp x A.hasFDerivAt).fderiv
    have hJac : coordinateJacobianMatrix (Xi2 ∘ A) x =
        coordinateJacobianMatrix Xi2 (A x) * coordinateJacobianMatrix A x := by
      simp only [coordinateJacobianMatrix_eq_operatorMatrixMap,hChain,A.fderiv,operatorMatrixMap_comp]
    rw [hJac,Matrix.det_mul]
    exact (hJac2 (A x) (hRoomU hx)).mul (isUnit_det_coordinateJacobianMatrix_continuousLinearEquiv A x)
  have hRange1New : ∀ x ∈ newRoom, (Xi1 ∘ A) x ∈ (radiusTwoOpens : Set R3) :=
    fun x hx => hRange1 (A x) (hRoomU hx)
  have hRange2New : ∀ x ∈ newRoom, (Xi2 ∘ A) x ∈ (radiusTwoOpens : Set R3) :=
    fun x hx => hRange2 (A x) (hRoomU hx)
  have hComposite1 := pullback_carrier_linear_reparameterization_eq_original_composite
    original1 c1 hOriginal1 hc1 Xi1 room hRoom (hSmooth1.mono hRoomU) hC1 A
  have hComposite2 := pullback_carrier_linear_reparameterization_eq_original_composite
    original2 c2 hOriginal2 hc2 Xi2 room hRoom (hSmooth2.mono hRoomU) hC2 A
  have hNormNew : pullbackMetric original1 (Xi1 ∘ A) 0 = 1 :=
    (hComposite1 h0NewRoom).symm.trans hNorm
  have hPulled1 := harmonic_coordinate_columns_preserved_by_linear_equiv c1 hc1 room hRoom hColumns1 A
  have hPulled2 := harmonic_coordinate_columns_preserved_by_linear_equiv c2 hc2 room hRoom hColumns2 A
  have hHarmonic1New : ∀ i : Fin 3, ∀ x ∈ newRoom,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric original1 (Xi1 ∘ A)) (fun z => z i)) x = 0 := by
    intro i x hx
    have hNear : pullbackMetric original1 (Xi1 ∘ A) =ᶠ[𝓝 x] pullbackMetric c1 A := by
      filter_upwards [hNewRoom.mem_nhds hx] with y hy
      exact (hComposite1 hy).symm
    exact (coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
      _ _ (fun z => z i) x hNear).trans (hPulled1 i x hx)
  have hHarmonic2New : ∀ i : Fin 3, ∀ x ∈ newRoom,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric original2 (Xi2 ∘ A)) (fun z => z i)) x = 0 := by
    intro i x hx
    have hNear : pullbackMetric original2 (Xi2 ∘ A) =ᶠ[𝓝 x] pullbackMetric c2 A := by
      filter_upwards [hNewRoom.mem_nhds hx] with y hy
      exact (hComposite2 hy).symm
    exact (coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
      _ _ (fun z => z i) x hNear).trans (hPulled2 i x hx)
  have hMetricsNew : EqOn (pullbackMetric original1 (Xi1 ∘ A)) (pullbackMetric original2 (Xi2 ∘ A)) newW := by
    intro x hx
    have hSame : c1 (A x) = c2 (A x) :=
      (hC1 hx.2).trans ((hMetrics hx.1).trans (hC2 hx.2).symm)
    have hSamePulled : pullbackMetric c1 A x = pullbackMetric c2 A x := by
      unfold pullbackMetric metricOperatorField
      rw [hSame]
    exact (hComposite1 hx.2).symm.trans (hSamePulled.trans (hComposite2 hx.2))
  have hKernelsNew : ∀ x : R3, ∀ hx : x ∈ newW, ∀ y : R3, ∀ hy : y ∈ newW, x ≠ y →
      G1 ⟨(Xi1 ∘ A) y,hRange1New y (hNewWRoom hy)⟩ ((Xi1 ∘ A) x) =
        G2 ⟨(Xi2 ∘ A) y,hRange2New y (hNewWRoom hy)⟩ ((Xi2 ∘ A) x) := by
    intro x hx y hy hxy
    exact hKernels (A x) hx.1 (A y) hy.1 (fun h => hxy (A.injective h))
  obtain ⟨a,ha,_,hNeg⟩ := hSide
  have hSideRoom : ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ room ∧
      {z ∈ ball (0 : R3) r | sep z < 0} ⊆ W ∩ room := by
    refine ⟨min a b,lt_min ha hb,ball_subset_ball (min_le_right a b),?_⟩
    intro z hz
    exact ⟨hNeg ⟨ball_subset_ball (min_le_left a b) hz.1,hz.2⟩,
      ball_subset_ball (min_le_right a b) hz.1⟩
  obtain ⟨hSepNew,hZeroNew,hNormalNew,hSideNew⟩ :=
    one_sided_separator_preserved_by_positive_triangular_linear_equiv sep room (W ∩ room)
      hRoom h0Room (hSep.mono hRoomU) hZero hNormal hSideRoom A c hc hThird
  obtain ⟨S,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hG1,hG2,hXi1,hXi2,hSepId,hSRoom,hSW,hPreserve⟩ :=
    exists_known_side_source_data_of_original_charts original1 original2 hOriginal1 hOriginal2
      K1 K2 G1 G2 hKernel1 hKernel2 newRoom hNewRoom h0NewRoom (Xi1 ∘ A) (Xi2 ∘ A)
      hXi1New hXi2New hInj1New hInj2New hJac1New hJac2New hRange1New hRange2New hNormNew
      hHarmonic1New hHarmonic2New newW hNewW hNewWRoom hMetricsNew hKernelsNew
      (fun x => c⁻¹ * sep (A x)) hSepNew hZeroNew hNormalNew hSideNew
  refine ⟨A,c,hc,hThird,S,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hG1,hG2,hXi1,hXi2,hSepId,?_,?_,?_⟩
  · intro x hx
    exact hRoomU (hSRoom hx)
  · rw [hSW]
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1,hx.2⟩
    · intro hx
      exact ⟨⟨hx.1,hSRoom hx.2⟩,hx.2⟩
  · intro s hMatch
    apply hPreserve s
    intro x hx
    exact hMatch (A x) hx.1

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
