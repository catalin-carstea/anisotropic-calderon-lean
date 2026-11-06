import Calderon.ActualLocalPositiveMetricCarrier
import Calderon.ActualParameterOrderedOriginalSourceTransfer
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError
  NativeSourceChartCalculus

theorem origin_mem_closure_of_one_sided_region
    (W : Set R3) (sep : R3 → ℝ) (hZero : sep 0 = 0)
    (hNormal : ∀ v : R3, fderiv ℝ sep 0 v = v 2)
    (hSide : ∃ a : ℝ, 0 < a ∧ {z ∈ ball (0 : R3) a | sep z < 0} ⊆ W) :
    (0 : R3) ∈ closure W := by
  obtain ⟨a,ha,hNeg⟩ := hSide
  by_contra hNot
  have hOpen : IsOpen (closure W)ᶜ := isClosed_closure.isOpen_compl
  have h0 : (0 : R3) ∈ (closure W)ᶜ ∩ ball (0 : R3) a := ⟨hNot,mem_ball_self ha⟩
  have hMin : IsLocalMin sep (0 : R3) := by
    change ∀ᶠ x in 𝓝 (0 : R3), sep 0 ≤ sep x
    filter_upwards [(hOpen.inter isOpen_ball).mem_nhds h0] with x hx
    rw [hZero]
    by_contra hNonneg
    exact hx.1 (subset_closure (hNeg ⟨hx.2,lt_of_not_ge hNonneg⟩))
  have hOne := hNormal (EuclideanSpace.single (2 : Fin 3) 1)
  rw [hMin.fderiv_eq_zero] at hOne
  norm_num at hOne

theorem injective_fderiv_of_unit_coordinate_jacobian
    (Xi : R3 → R3) (x : R3) (hJac : IsUnit (coordinateJacobianMatrix Xi x).det) :
    Function.Injective (fderiv ℝ Xi x) := by
  have hm : IsUnit (coordinateJacobianMatrix Xi x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hJac
  have hD : IsUnit (fderiv ℝ Xi x) := by
    have h := hm.map matrixOperatorAlgEquiv.toMonoidHom
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap] at h
    change IsUnit (matrixOperatorAlgEquiv (matrixOperatorAlgEquiv.symm (fderiv ℝ Xi x))) at h
    simpa only [AlgEquiv.apply_symm_apply] using h
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp hD).1

theorem exists_known_side_source_data_of_original_charts
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
    (hNormalized1 : pullbackMetric original1 Xi1 0 = 1)
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
    ∃ S : KnownSideSourceData,
      S.hreg = fixedDirichletRegularity ∧ S.hcalc = fixedSobolevCalculus ∧
      S.original1 = original1 ∧ S.original2 = original2 ∧
      S.K1 = K1 ∧ S.K2 = K2 ∧ S.G1 = G1 ∧ S.G2 = G2 ∧
      S.Xi1 = Xi1 ∧ S.Xi2 = Xi2 ∧ S.separating_function = sep ∧
      S.coordinateRoom ⊆ U ∧ S.W = W ∩ S.coordinateRoom ∧
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
  obtain ⟨a,ha,_,hNegative⟩ := hSide
  have hNewSide : ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ room ∧
      {z ∈ ball (0 : R3) r | sep z < 0} ⊆ W ∩ room := by
    refine ⟨min a b,lt_min ha hb,ball_subset_ball (min_le_right a b),?_⟩
    intro z hz
    exact ⟨hNegative ⟨ball_subset_ball (min_le_left a b) hz.1,hz.2⟩,
      ball_subset_ball (min_le_right a b) hz.1⟩
  have h0Closure : (0 : R3) ∈ closure (W ∩ room) := by
    obtain ⟨r,hr,_,hNeg⟩ := hNewSide
    exact origin_mem_closure_of_one_sided_region (W ∩ room) sep hZero hNormal ⟨r,hr,hNeg⟩
  have hCMatch : EqOn c1 c2 (W ∩ room) := by
    intro x hx
    exact (hC1 hx.2).trans ((hMetrics hx.1).trans (hC2 hx.2).symm)
  have hAtOrigin : c1 0 = c2 0 := by
    ext i j
    have hEntry : EqOn (fun x => c1 x i j) (fun x => c2 x i j) (W ∩ room) :=
      fun x hx => congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) (hCMatch hx)
    exact hEntry.closure (hc1.smooth i j).continuous (hc2.smooth i j).continuous h0Closure
  have hc1Origin : c1 0 = 1 := (hC1 h0Room).trans hNormalized1
  have hc2Origin : c2 0 = 1 := hAtOrigin.symm.trans hc1Origin
  let S : KnownSideSourceData := {
    hreg := fixedDirichletRegularity
    hcalc := fixedSobolevCalculus
    original1 := original1
    original2 := original2
    original1_admissible := hOriginal1
    original2_admissible := hOriginal2
    K1 := K1
    K2 := K2
    G1 := G1
    G2 := G2
    kernel1 := hKernel1
    kernel2 := hKernel2
    coordinateRoom := room
    coordinateRoom_open := hRoom
    origin_mem := h0Room
    Xi1 := Xi1
    Xi2 := Xi2
    Xi1_smooth := hSmooth1.mono hRoomU
    Xi2_smooth := hSmooth2.mono hRoomU
    Xi1_injective := fun x hx y hy hxy => hInjective1 (hRoomU hx) (hRoomU hy) hxy
    Xi2_injective := fun x hx y hy hxy => hInjective2 (hRoomU hx) (hRoomU hy) hxy
    Xi1_jacobian := fun x hx => hJac1 x (hRoomU hx)
    Xi2_jacobian := fun x hx => hJac2 x (hRoomU hx)
    Xi1_room := fun x hx => hRange1 x (hRoomU hx)
    Xi2_room := fun x hx => hRange2 x (hRoomU hx)
    g1 := c1
    g2 := c2
    g1_admissible := hc1
    g2_admissible := hc2
    carrier1 := hC1
    carrier2 := hC2
    g1_origin := hc1Origin
    g2_origin := hc2Origin
    harmonic_coordinates1 := hColumns1
    harmonic_coordinates2 := hColumns2
    W := W ∩ room
    W_open := hW.inter hRoom
    W_room := fun _ hx => hx.2
    metrics_match := hCMatch
    kernels_match := by
      intro x hx y hy hxy
      exact hKernels x hx.1 y hy.1 hxy
    separating_function := sep
    separating_function_smooth := hSep.mono hRoomU
    separating_function_zero := hZero
    separating_function_normal := hNormal
    one_sided_room := hNewSide }
  refine ⟨S,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hRoomU,rfl,?_⟩
  intro s hMatch x hx
  exact hMatch x hx.1

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
