import Calderon.ActualPairedSourceContactHessianFrame
import Calderon.ActualCommonSourceKnownRoom
import Calderon.ActualPhysicalKnownBallOriginalSourceData

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Distributions Matrix.Norms.Elementwise Matrix
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError
  ExteriorSource.FixedSourceJetFrame

theorem exists_actual_original_source_data_at_missing_known_point
    (original1 original2 : MatrixField)
    (hOriginal1 : IsAdmissibleMetric original1) (hOriginal2 : IsAdmissibleMetric original2)
    (hEnergy : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy original1 f = minimalEnergy original2 f)
    (K1 K2 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G1 G2 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hKernel1 : IsRadiusTwoSeparatelySmoothInverseSourceKernel original1 hOriginal1 K1 G1)
    (hKernel2 : IsRadiusTwoSeparatelySmoothInverseSourceKernel original2 hOriginal2 K2 G2)
    (physicalW : Set R3) (hPhysicalW : IsOpen physicalW) (hConnected : IsConnected physicalW)
    (hPhysicalRoom : physicalW ⊆ (radiusTwoOpens : Set R3))
    (hExterior : (exteriorAnnulusOpens : Set R3) ⊆ physicalW)
    (Phi : R3 → R3) (hPhiRoom : ∀ x ∈ physicalW, Phi x ∈ (radiusTwoOpens : Set R3))
    (hPhiSmooth : ContDiffOn ℝ ∞ Phi physicalW) (hPhiInj : Set.InjOn Phi physicalW)
    (hPhiJac : ∀ x ∈ physicalW, IsUnit (coordinateJacobianMatrix Phi x).det)
    (hIso : EqOn (pullbackMetric original1 Phi) original2 physicalW)
    (hFix : ∀ x ∈ (fixedExteriorSourceOpens : Set R3), Phi x = x)
    (hMatch : ∀ x ∈ physicalW,
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus original2 hOriginal2 x =
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus original1 hOriginal1 (Phi x))
    (hMissing : ∃ x ∈ (radiusTwoOpens : Set R3), x ∉ physicalW) :
    ∃ (center p q : R3) (S : KnownSideSourceData),
      closedBall center (1/4 : ℝ) ⊆ (radiusTwoOpens : Set R3) ∧
      ball center (1/4 : ℝ) ⊆ physicalW ∧
      p ∈ sphere center (1/4 : ℝ) ∧ p ∈ (radiusTwoOpens : Set R3) ∧
      ‖p‖ ≤ 1 ∧ p ∉ physicalW ∧ p ∈ closure physicalW ∧
      q ∈ (radiusTwoOpens : Set R3) ∧ ‖q‖ ≤ 1 ∧
      S.hreg = fixedDirichletRegularity ∧ S.hcalc = fixedSobolevCalculus ∧
      S.original1 = original1 ∧ S.original2 = original2 ∧
      S.K1 = K1 ∧ S.K2 = K2 ∧ S.G1 = G1 ∧ S.G2 = G2 ∧
      S.Xi1 0 = q ∧ S.Xi2 0 = p ∧
      ‖S.Xi1 0‖ ≤ 1 ∧ ‖S.Xi2 0‖ ≤ 1 ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
        radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
        radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x) := by
  obtain ⟨center, p, hClosed, hBallW, hSphere, hpR, hpNorm, hpNotW, hpClosure⟩ :=
    exists_known_touching_quarter_ball_of_missing_radiusTwo_point
      physicalW hPhysicalW hPhysicalRoom hExterior hMissing
  have hSource : (fixedExteriorSourceOpens : Set R3) ⊆ physicalW :=
    fun x hx => hExterior (fixedExteriorSourceOpens_le_annulus hx)
  have hMatchFrame : ∀ y ∈ physicalW, ∀ f : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        original2 hOriginal2 f y =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        original1 hOriginal1 f (Phi y) :=
    fun y hy f => congrFun (hMatch y hy) f
  have hMatchRoom : ∀ y ∈ physicalW, ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        original1 hOriginal1 s (Phi y) =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        original2 hOriginal2 s y :=
    fun y hy s => (hMatchFrame y hy s).symm
  have hDiff : ∀ y ∈ physicalW, DifferentiableAt ℝ Phi y :=
    fun y hy => (hPhiSmooth.contDiffAt (hPhysicalW.mem_nhds hy)).differentiableAt (by simp)
  have hMetric : ∀ y ∈ physicalW,
      original2 y = (D Phi y)ᵀ * original1 (Phi y) * D Phi y := by
    intro y hy
    rw [← hIso hy]
    change pullbackMetric original1 Phi y =
      (coordinateJacobianMatrix Phi y)ᵀ * original1 (Phi y) * coordinateJacobianMatrix Phi y
    simp only [pullbackMetric,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,coordinateJacobianMatrix_eq_operatorMatrixMap,
      Matrix.mul_assoc]
  obtain ⟨q, c, sJet, e1, e2, r0, V0, Z0, hq, hqNorm, hqFree, hpFree, hLimit, hContact,
      he1, he2, hqS, hpS, hE1q, hE2p, h0T1, h0T2, hSub1, hSub2, hFwd1, hFwd2, hInv1, hInv2,
      hFD1, hIX1, hJac1, hJac2, hGS1, hGS2, hGP1, hGP2, hCols1, hCols2, hPDE1, hPDE2,
      hG10, hG20, hr0, hBall0, hFree0, hV0, hpV0, hV0S, hV0Ball, hV0Branch, hZ0, hZ0Open,
      hZ0Ball, hZ0Closure, hZ0Match, hJets⟩ :=
    exists_radiusTwoSource_commonChart_contact_hessian_frame
      original1 original2 hOriginal1 hOriginal2 hEnergy physicalW hPhysicalW Phi hPhiRoom
      hDiff hMatchFrame hMetric p hpR hpClosure hpNorm
  obtain ⟨r, hr, hrr0, hBallRoom, hKnownOpen, h0Closure, hRoomBranch, hRoomMatch⟩ :=
    exists_common_source_chart_known_room original1 original2 hOriginal1 hOriginal2
      c e1 e2 he1 he2 p q hpS hqS hE1q hE2p physicalW hPhysicalW hpClosure
      Phi hLimit hMatchRoom r0 hr0
  have hX10 : (e1.symm : R3 → R3) 0 = q := by
    simpa only [hE1q] using e1.left_inv hqS
  have hX20 : (e2.symm : R3 → R3) 0 = p := by
    simpa only [hE2p] using e2.left_inv hpS
  have h0 : (0 : R3) ∈ ball (0 : R3) r := mem_ball_self hr
  have hSmooth1 : ContDiffOn ℝ ∞ (e1.symm : R3 → R3) (ball (0 : R3) r) :=
    hInv1.mono fun z hz => (hBallRoom hz).1
  have hSmooth2 : ContDiffOn ℝ ∞ (e2.symm : R3 → R3) (ball (0 : R3) r) :=
    hInv2.mono fun z hz => (hBallRoom hz).2
  have hInjective1 : Set.InjOn (e1.symm : R3 → R3) (ball (0 : R3) r) := by
    intro x hx y hy hxy
    calc
      x = e1 (e1.symm x) := (e1.right_inv (hBallRoom hx).1).symm
      _ = e1 (e1.symm y) := by rw [hxy]
      _ = y := e1.right_inv (hBallRoom hy).1
  have hInjective2 : Set.InjOn (e2.symm : R3 → R3) (ball (0 : R3) r) := by
    intro x hx y hy hxy
    calc
      x = e2 (e2.symm x) := (e2.right_inv (hBallRoom hx).2).symm
      _ = e2 (e2.symm y) := by rw [hxy]
      _ = y := e2.right_inv (hBallRoom hy).2
  have hJacBall1 : ∀ x ∈ ball (0 : R3) r, IsUnit (coordinateJacobianMatrix e1.symm x).det :=
    fun x hx => hJac1 x (hBallRoom hx).1
  have hJacBall2 : ∀ x ∈ ball (0 : R3) r, IsUnit (coordinateJacobianMatrix e2.symm x).det :=
    fun x hx => hJac2 x (hBallRoom hx).2
  have hRange1 : ∀ x ∈ ball (0 : R3) r, (e1.symm : R3 → R3) x ∈ (radiusTwoOpens : Set R3) :=
    fun x hx => hSub1 (e1.map_target (hBallRoom hx).1)
  have hRange2 : ∀ x ∈ ball (0 : R3) r, (e2.symm : R3 → R3) x ∈ (radiusTwoOpens : Set R3) :=
    fun x hx => hSub2 (e2.map_target (hBallRoom hx).2)
  have hAvoid : ∀ z ∈ ball (0 : R3) r,
      (e1.symm : R3 → R3) z ∉ (fixedExteriorSourceOpens : Set R3) ∧
      (e2.symm : R3 → R3) z ∉ (fixedExteriorSourceOpens : Set R3) := by
    intro z hz
    have hz0 := hFree0 z (ball_subset_ball hrr0 hz)
    exact ⟨fun h => hz0.1 (ball_subset_closedBall
        (show (e1.symm : R3 → R3) z ∈ ball fixedExteriorSourceCenter (1/8 : ℝ) from h)),
      fun h => hz0.2 (ball_subset_closedBall
        (show (e2.symm : R3 → R3) z ∈ ball fixedExteriorSourceCenter (1/8 : ℝ) from h))⟩
  have hHarmonic1 : ∀ i : Fin 3, ∀ x ∈ ball (0 : R3) r,
      coordinateFluxDivergence (metricDivergenceFlux
        (pullbackMetric original1 (e1.symm : R3 → R3)) (fun z => z i)) x = 0 := by
    intro i x hx
    rw [ExteriorSource.coordinateFluxDivergence_metricDivergenceFlux_coordinate]
    exact hCols1 x (hBallRoom hx).1 (hAvoid x hx).1 i
  have hHarmonic2 : ∀ i : Fin 3, ∀ x ∈ ball (0 : R3) r,
      coordinateFluxDivergence (metricDivergenceFlux
        (pullbackMetric original2 (e2.symm : R3 → R3)) (fun z => z i)) x = 0 := by
    intro i x hx
    rw [ExteriorSource.coordinateFluxDivergence_metricDivergenceFlux_coordinate]
    exact hCols2 x (hBallRoom hx).2 (hAvoid x hx).2 i
  have hBranch : ∀ z ∈ ball (0 : R3) r, (e2.symm : R3 → R3) z ∈ physicalW →
      (e1.symm : R3 → R3) z = Phi ((e2.symm : R3 → R3) z) :=
    fun z hz hzW => (hRoomBranch z ⟨hz, hzW⟩).symm
  have hTouch : (e2.symm : R3 → R3) 0 ∈ sphere center (1/4 : ℝ) := by
    rw [hX20]
    exact hSphere
  obtain ⟨A, cA, hcA, hDirection, S, hReg, hCalc, hOrig1, hOrig2, hK1, hK2, hG1, hG2,
      hXiS1, hXiS2, hSepS, hRoomS, hSW, hPreserve⟩ :=
    exists_original_source_data_of_physical_known_ball original1 original2
      hOriginal1 hOriginal2 K1 K2 G1 G2 hKernel1 hKernel2
      (ball (0 : R3) r) isOpen_ball h0 (e1.symm : R3 → R3) (e2.symm : R3 → R3)
      hSmooth1 hSmooth2 hInjective1 hInjective2 hJacBall1 hJacBall2 hRange1 hRange2
      hHarmonic1 hHarmonic2 physicalW hPhysicalW hConnected hPhysicalRoom hSource
      Phi hPhiRoom hPhiSmooth hPhiInj hPhiJac hIso hFix hMatch hBranch
      center (1/4 : ℝ) (by norm_num) hTouch hBallW
  have hS01 : S.Xi1 0 = q := by
    rw [hXiS1, Function.comp_apply, map_zero, hX10]
  have hS02 : S.Xi2 0 = p := by
    rw [hXiS2, Function.comp_apply, map_zero, hX20]
  refine ⟨center, p, q, S, hClosed, hBallW, hSphere, hpR, hpNorm, hpNotW, hpClosure,
    hq, hqNorm, hReg, hCalc, hOrig1, hOrig2, hK1, hK2, hG1, hG2, hS01, hS02, ?_, ?_,
    hPreserve⟩
  · rw [hS01]
    exact hqNorm
  · rw [hS02]
    exact hpNorm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
