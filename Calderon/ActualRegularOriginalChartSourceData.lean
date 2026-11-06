import Calderon.ActualUnnormalizedOriginalChartSourceData
import Calderon.ActualSeparatingCovectorAlignment

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Distributions Matrix.Norms.Elementwise Matrix
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError
  NativeSourceChartCalculus NormalCoordinatesFrame

theorem exists_room_harmonic_columns_after_linear_reparameterization
    (g : MatrixField) (hg : IsAdmissibleMetric g) (Xi : R3 → R3)
    (U : Set R3) (hU : IsOpen U) (h0 : (0 : R3) ∈ U)
    (hXi : ContDiffOn ℝ ∞ Xi U)
    (hJac : ∀ x ∈ U, IsUnit (coordinateJacobianMatrix Xi x).det)
    (hColumns : ∀ i : Fin 3, ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g Xi) (fun z => z i)) x = 0)
    (B : R3 ≃L[ℝ] R3) :
    ∃ a : ℝ, 0 < a ∧ closedBall (0 : R3) a ⊆ U ∧
      ∀ i : Fin 3, ∀ x ∈ B ⁻¹' ball (0 : R3) a,
        coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g (Xi ∘ B)) (fun z => z i)) x = 0 := by
  have hPB := contDiffOn_native_source_chart_pullbackMetric g hg Xi U hU hXi
  have hEntry : ∀ i j : Fin 3, ContDiffOn ℝ ∞ (fun x => pullbackMetric g Xi x i j) U :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hPB i) j
  have hPos : ∀ x ∈ U, (pullbackMetric g Xi x).PosDef := fun x hx =>
    pullbackMetric_posDef_of_injective_fderiv g hg Xi x
      (injective_fderiv_of_unit_coordinate_jacobian Xi x (hJac x hx))
  obtain ⟨a,ha,_,hBallU,G,hG,hEq⟩ :=
    exists_admissible_metric_eq_on_local_closed_ball (pullbackMetric g Xi) U hU h0 hEntry hPos
  have hBallSub : ball (0 : R3) a ⊆ U := ball_subset_closedBall.trans hBallU
  have hCarrier : EqOn G (pullbackMetric g Xi) (ball (0 : R3) a) :=
    fun _ hx => hEq (ball_subset_closedBall hx)
  have hGColumns : ∀ i : Fin 3, ∀ x ∈ ball (0 : R3) a,
      coordinateFluxDivergence (metricDivergenceFlux G (fun z => z i)) x = 0 := by
    intro i x hx
    have hNear : G =ᶠ[𝓝 x] pullbackMetric g Xi := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hCarrier hy
    exact (coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
      _ _ (fun z => z i) x hNear).trans (hColumns i x (hBallSub hx))
  have hTrans := harmonic_coordinate_columns_preserved_by_linear_equiv G hG
    (ball (0 : R3) a) isOpen_ball hGColumns B
  have hComposite := pullback_carrier_linear_reparameterization_eq_original_composite
    g G hg hG Xi (ball (0 : R3) a) isOpen_ball (hXi.mono hBallSub) hCarrier B
  refine ⟨a,ha,hBallU,?_⟩
  intro i x hx
  have hNear : pullbackMetric g (Xi ∘ B) =ᶠ[𝓝 x] pullbackMetric G B := by
    filter_upwards [(isOpen_ball.preimage B.continuous).mem_nhds hx] with y hy
    exact (hComposite hy).symm
  exact (coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
    _ _ (fun z => z i) x hNear).trans (hTrans i x hx)

theorem exists_known_side_source_data_of_regular_original_charts
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
    (hRegular : fderiv ℝ sep 0 ≠ 0)
    (hSide : ∃ a : ℝ, 0 < a ∧ ball (0 : R3) a ⊆ U ∧
      {z ∈ ball (0 : R3) a | sep z < 0} ⊆ W) :
    ∃ (A : R3 ≃L[ℝ] R3) (c : ℝ), 0 < c ∧ (∀ v : R3, fderiv ℝ sep 0 (A v) = c * v 2) ∧
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
  obtain ⟨B,hB⟩ := exists_continuousLinearEquiv_aligning_nonzero_covector (fderiv ℝ sep 0) hRegular
  obtain ⟨a1,ha1,hBallU1,hColumns1⟩ :=
    exists_room_harmonic_columns_after_linear_reparameterization original1 hOriginal1 Xi1
      U hU h0 hSmooth1 hJac1 hHarmonic1 B
  obtain ⟨a2,ha2,hBallU2,hColumns2⟩ :=
    exists_room_harmonic_columns_after_linear_reparameterization original2 hOriginal2 Xi2
      U hU h0 hSmooth2 hJac2 hHarmonic2 B
  let b := min a1 a2
  let room := ball (0 : R3) b
  have hb : 0 < b := lt_min ha1 ha2
  have hRoom : IsOpen room := isOpen_ball
  have h0Room : (0 : R3) ∈ room := mem_ball_self hb
  have hRoom1 : room ⊆ ball (0 : R3) a1 := ball_subset_ball (min_le_left a1 a2)
  have hRoom2 : room ⊆ ball (0 : R3) a2 := ball_subset_ball (min_le_right a1 a2)
  have hRoomU : room ⊆ U := hRoom1.trans (ball_subset_closedBall.trans hBallU1)
  let newRoom := B ⁻¹' room
  let newW := B ⁻¹' (W ∩ room)
  have hNewRoom : IsOpen newRoom := hRoom.preimage B.continuous
  have h0NewRoom : (0 : R3) ∈ newRoom := by
    change B (0 : R3) ∈ room
    simpa only [map_zero] using h0Room
  have hNewW : IsOpen newW := (hW.inter hRoom).preimage B.continuous
  have hNewWRoom : newW ⊆ newRoom := fun _ hx => hx.2
  have hXi1New : ContDiffOn ℝ ∞ (Xi1 ∘ B) newRoom :=
    (hSmooth1.mono hRoomU).comp B.contDiff.contDiffOn (fun _ hx => hx)
  have hXi2New : ContDiffOn ℝ ∞ (Xi2 ∘ B) newRoom :=
    (hSmooth2.mono hRoomU).comp B.contDiff.contDiffOn (fun _ hx => hx)
  have hInj1New : Set.InjOn (Xi1 ∘ B) newRoom := by
    intro x hx y hy hxy
    exact B.injective (hInjective1 (hRoomU hx) (hRoomU hy) hxy)
  have hInj2New : Set.InjOn (Xi2 ∘ B) newRoom := by
    intro x hx y hy hxy
    exact B.injective (hInjective2 (hRoomU hx) (hRoomU hy) hxy)
  have hJac1New : ∀ x ∈ newRoom, IsUnit (coordinateJacobianMatrix (Xi1 ∘ B) x).det := by
    intro x hx
    have hDX := (hSmooth1.contDiffAt (hU.mem_nhds (hRoomU hx))).differentiableAt (by simp)
    have hChain := (hDX.hasFDerivAt.comp x B.hasFDerivAt).fderiv
    have hJac : coordinateJacobianMatrix (Xi1 ∘ B) x =
        coordinateJacobianMatrix Xi1 (B x) * coordinateJacobianMatrix B x := by
      simp only [coordinateJacobianMatrix_eq_operatorMatrixMap,hChain,B.fderiv,operatorMatrixMap_comp]
    rw [hJac,Matrix.det_mul]
    exact (hJac1 (B x) (hRoomU hx)).mul (isUnit_det_coordinateJacobianMatrix_continuousLinearEquiv B x)
  have hJac2New : ∀ x ∈ newRoom, IsUnit (coordinateJacobianMatrix (Xi2 ∘ B) x).det := by
    intro x hx
    have hDX := (hSmooth2.contDiffAt (hU.mem_nhds (hRoomU hx))).differentiableAt (by simp)
    have hChain := (hDX.hasFDerivAt.comp x B.hasFDerivAt).fderiv
    have hJac : coordinateJacobianMatrix (Xi2 ∘ B) x =
        coordinateJacobianMatrix Xi2 (B x) * coordinateJacobianMatrix B x := by
      simp only [coordinateJacobianMatrix_eq_operatorMatrixMap,hChain,B.fderiv,operatorMatrixMap_comp]
    rw [hJac,Matrix.det_mul]
    exact (hJac2 (B x) (hRoomU hx)).mul (isUnit_det_coordinateJacobianMatrix_continuousLinearEquiv B x)
  have hRange1New : ∀ x ∈ newRoom, (Xi1 ∘ B) x ∈ (radiusTwoOpens : Set R3) :=
    fun x hx => hRange1 (B x) (hRoomU hx)
  have hRange2New : ∀ x ∈ newRoom, (Xi2 ∘ B) x ∈ (radiusTwoOpens : Set R3) :=
    fun x hx => hRange2 (B x) (hRoomU hx)
  have hHarmonic1New : ∀ i : Fin 3, ∀ x ∈ newRoom,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric original1 (Xi1 ∘ B)) (fun z => z i)) x = 0 :=
    fun i x hx => hColumns1 i x (hRoom1 hx)
  have hHarmonic2New : ∀ i : Fin 3, ∀ x ∈ newRoom,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric original2 (Xi2 ∘ B)) (fun z => z i)) x = 0 :=
    fun i x hx => hColumns2 i x (hRoom2 hx)
  have hExpand (g : MatrixField) (X : R3 → R3) (x : R3) :
      pullbackMetric g X x = (operatorMatrixMap (fderiv ℝ X x))ᵀ *
        (g (X x) * operatorMatrixMap (fderiv ℝ X x)) := by
    simp only [pullbackMetric,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,Matrix.mul_assoc]
  have hComposition (g : MatrixField) (X : R3 → R3) (hX : ContDiffOn ℝ ∞ X U)
      (x : R3) (hx : x ∈ newRoom) :
      pullbackMetric g (X ∘ B) x = (operatorMatrixMap (B : R3 →L[ℝ] R3))ᵀ *
        (pullbackMetric g X (B x) * operatorMatrixMap (B : R3 →L[ℝ] R3)) := by
    have hD := (hX.contDiffAt (hU.mem_nhds (hRoomU hx))).differentiableAt (by simp)
    have hChain := (hD.hasFDerivAt.comp x B.hasFDerivAt).fderiv
    rw [hExpand g (X ∘ B) x,hChain,operatorMatrixMap_comp,Matrix.transpose_mul,
      hExpand g X (B x)]
    simp only [Function.comp_apply,Matrix.mul_assoc]
  have hMetricsNew : EqOn (pullbackMetric original1 (Xi1 ∘ B)) (pullbackMetric original2 (Xi2 ∘ B)) newW := by
    intro x hx
    rw [hComposition original1 Xi1 hSmooth1 x hx.2,hComposition original2 Xi2 hSmooth2 x hx.2,
      hMetrics hx.1]
  have hKernelsNew : ∀ x : R3, ∀ hx : x ∈ newW, ∀ y : R3, ∀ hy : y ∈ newW, x ≠ y →
      G1 ⟨(Xi1 ∘ B) y,hRange1New y (hNewWRoom hy)⟩ ((Xi1 ∘ B) x) =
        G2 ⟨(Xi2 ∘ B) y,hRange2New y (hNewWRoom hy)⟩ ((Xi2 ∘ B) x) := by
    intro x hx y hy hxy
    exact hKernels (B x) hx.1 (B y) hy.1 (fun h => hxy (B.injective h))
  have hSepNew : ContDiffOn ℝ ∞ (sep ∘ B) newRoom :=
    (hSep.mono hRoomU).comp B.contDiff.contDiffOn (fun _ hx => hx)
  have hZeroNew : (sep ∘ B) (0 : R3) = 0 := by simpa only [Function.comp_apply,map_zero] using hZero
  have hNormalNew : ∀ v : R3, fderiv ℝ (sep ∘ B) 0 v = v 2 := by
    have hDsep := (hSep.contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp)
    have hAtB : HasFDerivAt sep (fderiv ℝ sep 0) (B (0 : R3)) := by
      simpa only [map_zero] using hDsep.hasFDerivAt
    have hD : HasFDerivAt (sep ∘ B) ((fderiv ℝ sep 0).comp B.toContinuousLinearMap) (0 : R3) :=
      hAtB.comp 0 B.hasFDerivAt
    intro v
    rw [hD.fderiv]
    exact hB v
  obtain ⟨a,ha,_,hNeg⟩ := hSide
  have hPreOpen : IsOpen (B ⁻¹' ball (0 : R3) (min a b)) := isOpen_ball.preimage B.continuous
  have h0Pre : (0 : R3) ∈ B ⁻¹' ball (0 : R3) (min a b) := by
    simpa only [mem_preimage,map_zero] using mem_ball_self (lt_min ha hb)
  obtain ⟨t,ht,hSmall⟩ := Metric.isOpen_iff.mp hPreOpen 0 h0Pre
  have hSideNew : ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ newRoom ∧
      {z ∈ ball (0 : R3) r | (sep ∘ B) z < 0} ⊆ newW := by
    have hRoomSmall : ball (0 : R3) t ⊆ newRoom :=
      fun z hz => by
        change B z ∈ ball (0 : R3) b
        exact (ball_subset_ball (min_le_right a b) : ball (0 : R3) (min a b) ⊆ ball (0 : R3) b) (hSmall hz)
    refine ⟨t,ht,hRoomSmall,?_⟩
    intro z hz
    have hzA : B z ∈ ball (0 : R3) a :=
      (ball_subset_ball (min_le_left a b) : ball (0 : R3) (min a b) ⊆ ball (0 : R3) a) (hSmall hz.1)
    exact ⟨hNeg ⟨hzA,hz.2⟩,hRoomSmall hz.1⟩
  obtain ⟨A,c,hc,hThird,S,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hG1,hG2,hXi1,hXi2,hSepId,hSRoom,hSW,hPreserve⟩ :=
    exists_known_side_source_data_of_unnormalized_original_charts original1 original2 hOriginal1 hOriginal2
      K1 K2 G1 G2 hKernel1 hKernel2 newRoom hNewRoom h0NewRoom (Xi1 ∘ B) (Xi2 ∘ B)
      hXi1New hXi2New hInj1New hInj2New hJac1New hJac2New hRange1New hRange2New
      hHarmonic1New hHarmonic2New newW hNewW hNewWRoom hMetricsNew hKernelsNew
      (sep ∘ B) hSepNew hZeroNew hNormalNew hSideNew
  let C := A.trans B
  have hDirection : ∀ v : R3, fderiv ℝ sep 0 (C v) = c * v 2 := by
    intro v
    change fderiv ℝ sep 0 (B (A v)) = c * v 2
    rw [hB]
    exact hThird v
  have hXi1Final : S.Xi1 = Xi1 ∘ C := by rw [hXi1]; rfl
  have hXi2Final : S.Xi2 = Xi2 ∘ C := by rw [hXi2]; rfl
  have hSepFinal : S.separating_function = (fun x => c⁻¹ * sep (C x)) := by rw [hSepId]; rfl
  refine ⟨C,c,hc,hDirection,S,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hG1,hG2,hXi1Final,hXi2Final,hSepFinal,?_,?_,?_⟩
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
    exact hMatch (B x) hx.1

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
