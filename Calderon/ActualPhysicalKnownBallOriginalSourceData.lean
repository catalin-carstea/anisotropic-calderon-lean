import Calderon.ActualRegularOriginalChartSourceData
import Calderon.ActualKnownBallGeometry
import Calderon.ActualKnownIsometryChartMatching

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Distributions Matrix.Norms.Elementwise Matrix
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError

theorem exists_original_source_data_of_physical_known_ball
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
    (physicalW : Set R3) (hPhysicalW : IsOpen physicalW) (hConnected : IsConnected physicalW)
    (hPhysicalRoom : physicalW ⊆ (radiusTwoOpens : Set R3))
    (hSource : (fixedExteriorSourceOpens : Set R3) ⊆ physicalW)
    (Phi : R3 → R3) (hPhiRoom : ∀ x ∈ physicalW, Phi x ∈ (radiusTwoOpens : Set R3))
    (hPhiSmooth : ContDiffOn ℝ ∞ Phi physicalW) (hPhiInj : Set.InjOn Phi physicalW)
    (hPhiJac : ∀ x ∈ physicalW, IsUnit (coordinateJacobianMatrix Phi x).det)
    (hIso : EqOn (pullbackMetric original1 Phi) original2 physicalW)
    (hFix : ∀ x ∈ (fixedExteriorSourceOpens : Set R3), Phi x = x)
    (hMatch : ∀ x ∈ physicalW,
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus original2 hOriginal2 x =
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus original1 hOriginal1 (Phi x))
    (hBranch : ∀ z ∈ U, Xi2 z ∈ physicalW → Xi1 z = Phi (Xi2 z))
    (center : R3) (r : ℝ) (hr : 0 < r)
    (hTouch : Xi2 0 ∈ sphere center r) (hBall : ball center r ⊆ physicalW) :
    ∃ (A : R3 ≃L[ℝ] R3) (c : ℝ), 0 < c ∧ (∀ v : R3, fderiv ℝ (fun z => ‖Xi2 z - center‖ ^ 2 - r ^ 2) 0 (A v) = c * v 2) ∧
    ∃ S : KnownSideSourceData,
      S.hreg = fixedDirichletRegularity ∧ S.hcalc = fixedSobolevCalculus ∧
      S.original1 = original1 ∧ S.original2 = original2 ∧
      S.K1 = K1 ∧ S.K2 = K2 ∧ S.G1 = G1 ∧ S.G2 = G2 ∧
      S.Xi1 = Xi1 ∘ A ∧ S.Xi2 = Xi2 ∘ A ∧
      S.separating_function = (fun x => c⁻¹ * (‖Xi2 (A x) - center‖ ^ 2 - r ^ 2)) ∧
      S.coordinateRoom ⊆ A ⁻¹' U ∧ S.W = (A ⁻¹' (U ∩ Xi2 ⁻¹' physicalW)) ∩ S.coordinateRoom ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
        radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
        radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x) := by
  let W := U ∩ Xi2 ⁻¹' physicalW
  have hW : IsOpen W := hSmooth2.continuousOn.isOpen_inter_preimage hU hPhysicalW
  have hWU : W ⊆ U := fun _ hx => hx.1
  have hXi2W : Set.MapsTo Xi2 W physicalW := fun _ hx => hx.2
  have hXi1 : EqOn Xi1 (Phi ∘ Xi2) W := fun _ hx => hBranch _ hx.1 hx.2
  obtain ⟨hKnownRange,hKnownSmooth,hMetrics,hKernels,hKnown⟩ :=
    original_chart_matching_fields_of_known_isometry original1 original2 hOriginal1 hOriginal2
      K1 K2 G1 G2 hKernel1 hKernel2 physicalW hPhysicalW hConnected hPhysicalRoom hSource
      Phi hPhiRoom hPhiSmooth hPhiInj hPhiJac hIso hFix hMatch
      W hW Xi1 Xi2 (hSmooth2.mono hWU) (hInjective2.mono hWU) hXi2W hXi1
  obtain ⟨sep,hSepId,hSep,hZero,hRegular,a,ha,hBallU,hNegative⟩ :=
    exists_regular_one_sided_separator_of_known_physical_ball U physicalW hU h0 Xi2 hSmooth2
      (hJac2 0 h0) center r hr hTouch hBall
  have hSide : ∃ b : ℝ, 0 < b ∧ ball (0 : R3) b ⊆ U ∧
      {z ∈ ball (0 : R3) b | sep z < 0} ⊆ W := by
    refine ⟨a,ha,hBallU,?_⟩
    intro z hz
    exact ⟨hBallU hz.1,hNegative hz⟩
  have hKernelsExact : ∀ x : R3, ∀ hx : x ∈ W, ∀ y : R3, ∀ hy : y ∈ W, x ≠ y →
      G1 ⟨Xi1 y,hRange1 y (hWU hy)⟩ (Xi1 x) = G2 ⟨Xi2 y,hRange2 y (hWU hy)⟩ (Xi2 x) := by
    intro x hx y hy hxy
    exact hKernels x hx y hy hxy
  obtain ⟨A,c,hc,hDirection,S,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hG1,hG2,hXiS1,hXiS2,hSepS,hRoom,hSW,hPreserve⟩ :=
    exists_known_side_source_data_of_regular_original_charts original1 original2 hOriginal1 hOriginal2
      K1 K2 G1 G2 hKernel1 hKernel2 U hU h0 Xi1 Xi2 hSmooth1 hSmooth2 hInjective1 hInjective2
      hJac1 hJac2 hRange1 hRange2 hHarmonic1 hHarmonic2 W hW hWU hMetrics hKernelsExact
      sep hSep hZero hRegular hSide
  have hDirectionExact : ∀ v : R3,
      fderiv ℝ (fun z => ‖Xi2 z - center‖ ^ 2 - r ^ 2) 0 (A v) = c * v 2 := by
    rw [← hSepId]
    exact hDirection
  have hSepExact : S.separating_function = (fun x => c⁻¹ * (‖Xi2 (A x) - center‖ ^ 2 - r ^ 2)) := by
    rw [hSepS,hSepId]
  refine ⟨A,c,hc,hDirectionExact,S,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hG1,hG2,hXiS1,hXiS2,hSepExact,hRoom,hSW,?_⟩
  intro s
  exact hPreserve s (hKnown s)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
