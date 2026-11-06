import TaskInterface
import Calderon.ActualMixedKernelGlobalSurfaceExtension
import Calderon.LocalMetricPullbackDivergence
import Calderon.RadiusTwoCompactMetricDensitySupport
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem exists_contDiff_compact_extension_support_subset_eq_near_compact
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A U : Set R3) (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    (psi : R3 → F) (hpsi : ContDiffOn ℝ ∞ psi U) :
    ∃ psiGlobal : R3 → F, ContDiff ℝ ∞ psiGlobal ∧ HasCompactSupport psiGlobal ∧
      tsupport psiGlobal ⊆ U ∧
      (∀ x, psi x = 0 → psiGlobal x = 0) ∧ ∀ y ∈ A, psiGlobal =ᶠ[𝓝 y] psi := by
  obtain ⟨W,hW,hAW,hWcompact⟩ := exists_isOpen_superset_and_isCompact_closure hA
  have hAUW : A ⊆ U ∩ W := fun x hx => ⟨hAU hx,hAW hx⟩
  obtain ⟨B,hB,hAB,hBclosure⟩ :=
    hA.exists_isOpen_closure_subset ((hU.inter hW).mem_nhdsSet.mpr hAUW)
  have hBcompact : IsCompact (closure B) :=
    hWcompact.of_isClosed_subset isClosed_closure
      (fun x hx => subset_closure (hBclosure hx).2)
  obtain ⟨C,hC,hAC,hCclosure⟩ :=
    hA.exists_isOpen_closure_subset (hB.mem_nhdsSet.mpr hAB)
  obtain ⟨chi,hchi,_,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hB isClosed_closure hCclosure
  have hSmooth : ContDiff ℝ ∞ (fun x => chi x • psi x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hchi.contDiffAt.smul (hpsi.contDiffAt (hU.mem_nhds hx))
    · have hxOutside : x ∈ (closure B)ᶜ := fun hxB => hx (hBclosure hxB).1
      have hZero : (fun y => chi y • psi y) =ᶠ[𝓝 x] (fun _ : R3 => (0 : F)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxOutside] with y hy
        have hchiZero : chi y = 0 := by
          apply notMem_support.mp
          rw [hSupport]
          exact fun hyB => hy (subset_closure hyB)
        simp only [hchiZero,zero_smul]
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : R3 => (0 : F)) x).congr_of_eventuallyEq hZero
  have hSub : Function.support (fun y => chi y • psi y) ⊆ B := by
    intro x hx
    by_contra hn
    have hZero : chi x = 0 := by
      apply notMem_support.mp
      rwa [hSupport]
    exact hx (by simp only [hZero,zero_smul])
  have hCompact : HasCompactSupport (fun x => chi x • psi x) :=
    hBcompact.of_isClosed_subset isClosed_closure (closure_mono hSub)
  refine ⟨fun x => chi x • psi x,hSmooth,hCompact,?_,?_,?_⟩
  · intro x hx
    change x ∈ closure (Function.support (fun y => chi y • psi y)) at hx
    exact (hBclosure ((closure_mono hSub) hx)).1
  · intro x hx
    simp only [hx,smul_zero]
  intro x hx
  filter_upwards [hC.mem_nhds (hAC hx)] with y hy
  have hchiOne : chi y = 1 := (hOne y).mp (subset_closure hy)
  simp only [hchiOne,one_smul]

theorem exists_contDiff_compact_extension_eqOn_of_support_inter_subset
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A U : Set R3) (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    (psi : R3 → F) (hpsi : ContDiffOn ℝ ∞ psi U)
    (hSupport : Function.support psi ∩ U ⊆ A) :
    ∃ psiGlobal : R3 → F, ContDiff ℝ ∞ psiGlobal ∧ HasCompactSupport psiGlobal ∧
      tsupport psiGlobal ⊆ U ∧ EqOn psiGlobal psi U := by
  obtain ⟨psiGlobal,hSmooth,hCompact,hSub,hZero,hNear⟩ :=
    exists_contDiff_compact_extension_support_subset_eq_near_compact A U hA hU hAU psi hpsi
  refine ⟨psiGlobal,hSmooth,hCompact,hSub,?_⟩
  intro x hx
  by_cases h : psi x = 0
  · exact (hZero x h).trans h.symm
  · exact (hNear x (hSupport ⟨h,hx⟩)).eq_of_nhds

theorem exists_compact_testFunction_pushforward_openPartialHomeomorph
    (U V : TopologicalSpace.Opens R3) (e : OpenPartialHomeomorph R3 R3)
    (hSource : e.source = (U : Set R3))
    (hInverse : ContDiffOn ℝ ∞ e.symm e.target)
    (hTarget : e.target ⊆ (V : Set R3)) (psi : 𝓓(U,ℝ)) :
    ∃ phi : 𝓓(V,ℝ), tsupport (phi : R3 → ℝ) ⊆ e.target ∧
      ∀ z ∈ (U : Set R3), phi (e z) = psi z := by
  let A : Set R3 := e '' tsupport (psi : R3 → ℝ)
  have hSupportSource : tsupport (psi : R3 → ℝ) ⊆ e.source := by
    rw [hSource]
    exact psi.tsupport_subset
  have hA : IsCompact A :=
    psi.hasCompactSupport.image_of_continuousOn (e.continuousOn.mono hSupportSource)
  have hInside : A ⊆ e.target := by
    rintro x ⟨z,hz,rfl⟩
    exact e.map_source (hSupportSource hz)
  let f : R3 → ℝ := fun x => psi (e.symm x)
  have hSmooth : ContDiffOn ℝ ∞ f e.target := psi.contDiff.comp_contDiffOn hInverse
  have hLocalSupport : Function.support f ∩ e.target ⊆ A := by
    intro x hx
    have hNonzero : psi (e.symm x) ≠ 0 := hx.1
    have hAt : e.symm x ∈ tsupport (psi : R3 → ℝ) := subset_closure hNonzero
    exact ⟨e.symm x,hAt,e.right_inv hx.2⟩
  obtain ⟨Phi,hPhi,hCompact,hSupport,hEq⟩ :=
    exists_contDiff_compact_extension_eqOn_of_support_inter_subset
      A e.target hA e.open_target hInside f hSmooth hLocalSupport
  let phi : 𝓓(V,ℝ) := ⟨Phi,hPhi,hCompact,hSupport.trans hTarget⟩
  refine ⟨phi,hSupport,?_⟩
  intro z hz
  have hzSource : z ∈ e.source := by rwa [hSource]
  exact (hEq (e.map_source hzSource)).trans
    (congrArg (fun t : R3 => psi t) (e.left_inv hzSource))

open ExteriorSource EnergyBridge MetricVolume MetricOperator ConnectionError

theorem radiusTwoCompactMetricTestDensity_eq_neg_coordinateFluxDivergence
    (g : MatrixField) (hg : IsAdmissibleMetric g) (phi : 𝓓(radiusTwoOpens,ℝ)) (x : R3) :
    (radiusTwoCompactMetricTestDensity g hg phi).1 x =
      -coordinateFluxDivergence (metricDivergenceFlux g (phi : R3 → ℝ)) x := by
  have hFlux (i : Fin 3) : radiusTwoCompactMetricFlux g phi i =
      fun z => metricDivergenceFlux g (phi : R3 → ℝ) z i := by
    funext z
    unfold radiusTwoCompactMetricFlux metricDivergenceFlux
    rw [matrixOperator_coordinate]
    apply Finset.sum_congr rfl
    intro j _
    rw [gradient_coordinate]
  change -(∑ i : Fin 3, fderiv ℝ (radiusTwoCompactMetricFlux g phi i) x
      (MetricVolume.coordinateVector i)) = _
  simp only [hFlux,coordinateFluxDivergence]
  rfl

theorem coordinateJacobianMatrix_det_eq_fderiv_det (F : R3 → R3) (x : R3) :
    (coordinateJacobianMatrix F x).det = (fderiv ℝ F x).det := by
  rw [coordinateJacobianMatrix_eq_operatorMatrixMap]
  have hLin : (operatorMatrixMap (fderiv ℝ F x)).toLpLin 2 2 =
      (fderiv ℝ F x).toLinearMap := by
    ext z i
    exact congrArg (fun v : R3 => v i) (operatorMatrixMap_apply (fderiv ℝ F x) z)
  have h := LinearMap.det_toLpLin 2 (operatorMatrixMap (fderiv ℝ F x))
  rw [hLin] at h
  exact h.symm

/-- Smooth forward and inverse chart maps force the exact coordinate determinant to be a unit. -/
theorem coordinateJacobianMatrix_isUnit_of_smooth_open_chart
    (F : R3 → R3) (hF : ContDiff ℝ ∞ F)
    (e : OpenPartialHomeomorph R3 R3) (he : (e : R3 → R3) = F)
    (hInverse : ContDiffOn ℝ ∞ e.symm e.target)
    (z : R3) (hz : z ∈ e.source) : IsUnit (coordinateJacobianMatrix F z).det := by
  have hDX := (hInverse.contDiffAt (e.open_target.mem_nhds (e.map_source hz))).differentiableAt (by simp)
  have hDF := hF.differentiable (by simp) z
  have hNear : (e.symm : R3 → R3) ∘ F =ᶠ[𝓝 z] (fun t : R3 => t) := by
    filter_upwards [e.open_source.mem_nhds hz] with t ht
    simpa only [he,Function.comp_apply] using e.left_inv ht
  have hId : fderiv ℝ (fun t : R3 => t) z = ContinuousLinearMap.id ℝ R3 :=
    (ContinuousLinearMap.id ℝ R3).hasFDerivAt.fderiv
  have hDX' : DifferentiableAt ℝ (e.symm : R3 → R3) (F z) := by
    simpa only [he] using hDX
  have hProd : (fderiv ℝ e.symm (F z)).comp (fderiv ℝ F z) =
      ContinuousLinearMap.id ℝ R3 :=
    ((hDX'.hasFDerivAt.comp z hDF.hasFDerivAt).fderiv).symm.trans
      (hNear.fderiv_eq.trans hId)
  have hMat := congrArg operatorMatrixMap hProd
  have hOpId : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) := matrixOperatorAlgEquiv.symm.map_one
  rw [operatorMatrixMap_comp,hOpId] at hMat
  have hDet : (operatorMatrixMap (fderiv ℝ e.symm (F z))).det *
      (operatorMatrixMap (fderiv ℝ F z)).det = 1 := by
    simpa only [Matrix.det_mul,Matrix.det_one] using congrArg Matrix.det hMat
  apply isUnit_iff_ne_zero.mpr
  rw [coordinateJacobianMatrix_eq_operatorMatrixMap]
  intro hZero
  rw [hZero,mul_zero] at hDet
  exact zero_ne_one hDet

theorem original_first_kernel_pointSource_pullback
    (S : KnownSideSourceData) (F : R3 → R3) (hF : ContDiff ℝ ∞ F)
    (e : OpenPartialHomeomorph R3 R3) (he : (e : R3 → R3) = F)
    (hSource : e.source = ball (0 : R3) 2)
    (hInverse : ContDiffOn ℝ ∞ e.symm e.target)
    (hTarget : e.target ⊆ (radiusTwoOpens : Set R3))
    (pole : (radiusTwoOpens : Set R3)) (hPole : F 0 = (pole : R3))
    (hJac : ∀ z ∈ ball (0 : R3) 2, IsUnit (coordinateJacobianMatrix F z).det)
    (psi : 𝓓(radiusTwoOpens,ℝ)) :
    (∫ z in ball (0 : R3) 2, S.G1 pole (F z) *
      (-coordinateFluxDivergence
        (metricDivergenceFlux (pullbackMetric S.original1 F) (psi : R3 → ℝ)) z)
      ∂(volume : Measure R3)) = psi (0 : R3)
 := by
  classical
  have hSource' : e.source = (radiusTwoOpens : Set R3) := by
    exact hSource
  obtain ⟨phi,hSupport,hPull⟩ := exists_compact_testFunction_pushforward_openPartialHomeomorph
    radiusTwoOpens radiusTwoOpens e hSource' hInverse hTarget psi
  have hSourceDensity : ∀ z ∈ ball (0 : R3) 2,
      -coordinateFluxDivergence
        (metricDivergenceFlux (pullbackMetric S.original1 F) (psi : R3 → ℝ)) z =
      |(coordinateJacobianMatrix F z).det| *
        (radiusTwoCompactMetricTestDensity S.original1 S.original1_admissible phi).1 (F z) := by
    intro z hz
    have hPullNear : ((phi : R3 → ℝ) ∘ F) =ᶠ[𝓝 z] (psi : R3 → ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with t ht
      have h := hPull t (by exact ht)
      simpa only [he,Function.comp_apply] using h
    have hCongr := coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
      (pullbackMetric S.original1 F) ((phi : R3 → ℝ) ∘ F) (psi : R3 → ℝ) z hPullNear
    rw [← hCongr,coordinateFluxDivergence_metricDivergenceFlux_pullbackMetric
      S.original1 S.original1_admissible.smooth S.original1_admissible.posDef F
      (phi : R3 → ℝ) hF phi.contDiff z (hJac z hz),
      radiusTwoCompactMetricTestDensity_eq_neg_coordinateFluxDivergence]
    ring
  let Q : R3 → ℝ := fun x => S.G1 pole x *
    (radiusTwoCompactMetricTestDensity S.original1 S.original1_admissible phi).1 x
  have hRestrict : (∫ x in radiusTwoOpens, Q x ∂(volume : Measure R3)) =
      ∫ x in e.target, Q x ∂(volume : Measure R3) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      radiusTwoOpens.isOpen.measurableSet hTarget
    intro x hx
    have hNot : x ∉ tsupport (phi : R3 → ℝ) := fun h => hx.2 (hSupport h)
    dsimp only [Q]
    rw [radiusTwoCompactMetricTestDensity_eq_zero_of_notMem_tsupport
      S.original1 S.original1_admissible phi x hNot,mul_zero]
  have hChange := integral_target_eq_integral_abs_det_fderiv_smul
    (volume : Measure R3) (f := e) (f' := fderiv ℝ F)
    (fun x hx => by simpa only [he] using hF.differentiable (by simp) x |>.hasFDerivAt) Q
  have hIntegral : (∫ z in ball (0 : R3) 2, S.G1 pole (F z) *
      (-coordinateFluxDivergence
        (metricDivergenceFlux (pullbackMetric S.original1 F) (psi : R3 → ℝ)) z)
      ∂(volume : Measure R3)) = ∫ x in e.target, Q x ∂(volume : Measure R3) := by
    rw [hChange,hSource]
    apply setIntegral_congr_fun isOpen_ball.measurableSet
    intro z hz
    dsimp only
    rw [hSourceDensity z hz,coordinateJacobianMatrix_det_eq_fderiv_det]
    simp only [he,smul_eq_mul,Q]
    ring
  calc
    _ = ∫ x in e.target, Q x ∂(volume : Measure R3) := hIntegral
    _ = ∫ x in radiusTwoOpens, Q x ∂(volume : Measure R3) := hRestrict.symm
    _ = phi (pole : R3) := (S.kernel1.1.1 pole).2.2.2.2.2 phi
    _ = psi (0 : R3) := by
      rw [← hPole]
      have h := hPull 0 (by change (0 : R3) ∈ ball (0 : R3) 2; simp)
      simpa only [he] using h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
