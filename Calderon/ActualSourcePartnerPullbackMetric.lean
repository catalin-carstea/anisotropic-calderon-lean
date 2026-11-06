import Calderon.ExteriorIdentityHomeomorphExtension
import Calderon.NativeSourceChartPullbackSmoothness
import Calderon.NativeSourceChartPullbackPositivity
import Calderon.NativeSourceChartInverseConditioning
import Calderon.LocalMetricPullbackDivergence
import Calderon.RadiusTwoSmoothSourceClassicalEquation
import Calderon.ActualSourceChartHarmonicColumns
import Calderon.ActualFiniteCompatibleSourceJetsFromUniqueContinuation
import Calderon.MetricHessianTestInjectivity

/-! HELD M5 native antecedents: actual pullback admissibility, SAME-source PDE,
and the constructed positive smooth scalar relation. No metric comparison input. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped BigOperators ContDiff Topology Matrix Distributions
open scoped Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature ConnectionError MetricOperator MetricVolume
  NativeSourceChartCalculus MetricCompatibleSourceJetAlgebra

lemma fderiv_symm_comp_fderiv_of_smooth_equiv
    (Phi : R3 ≃ R3) (hPhi : ContDiff ℝ ∞ (Phi : R3 → R3))
    (hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3)) (x : R3) :
    (fderiv ℝ (Phi.symm : R3 → R3) (Phi x)).comp
      (fderiv ℝ (Phi : R3 → R3) x) = ContinuousLinearMap.id ℝ R3 := by
  have hComp := ((hInv.differentiable (by simp) (Phi x)).hasFDerivAt).comp x
    ((hPhi.differentiable (by simp) x).hasFDerivAt)
  have hFunction : (fun y : R3 => Phi.symm (Phi y)) = (id : R3 → R3) :=
    funext Phi.symm_apply_apply
  change HasFDerivAt (fun y : R3 => Phi.symm (Phi y))
    ((fderiv ℝ (Phi.symm : R3 → R3) (Phi x)).comp
      (fderiv ℝ (Phi : R3 → R3) x)) x at hComp
  rw [hFunction] at hComp
  exact hComp.unique (hasFDerivAt_id x)

lemma injective_fderiv_of_smooth_equiv
    (Phi : R3 ≃ R3) (hPhi : ContDiff ℝ ∞ (Phi : R3 → R3))
    (hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3)) (x : R3) :
    Function.Injective (fderiv ℝ (Phi : R3 → R3) x) := by
  have hProd := fderiv_symm_comp_fderiv_of_smooth_equiv Phi hPhi hInv x
  intro v w h
  have hBack := congrArg (fderiv ℝ (Phi.symm : R3 → R3) (Phi x)) h
  simpa only [← ContinuousLinearMap.comp_apply, hProd,
    ContinuousLinearMap.id_apply] using hBack

lemma isUnit_det_D_of_smooth_equiv
    (Phi : R3 ≃ R3) (hPhi : ContDiff ℝ ∞ (Phi : R3 → R3))
    (hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3)) (x : R3) :
    IsUnit (D (Phi : R3 → R3) x).det := by
  have hProd := fderiv_symm_comp_fderiv_of_smooth_equiv Phi hPhi hInv x
  have hMat := congrArg operatorMatrixMap hProd
  have hId : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) := matrixOperatorAlgEquiv.symm.map_one
  have hD : D (Phi : R3 → R3) x =
      operatorMatrixMap (fderiv ℝ (Phi : R3 → R3) x) :=
    coordinateJacobianMatrix_eq_operatorMatrixMap (Phi : R3 → R3) x
  rw [operatorMatrixMap_comp, hId, ← hD] at hMat
  have hDet := congrArg Matrix.det hMat
  rw [Matrix.det_mul, Matrix.det_one] at hDet
  apply isUnit_iff_ne_zero.mpr
  intro hZero
  rw [hZero, mul_zero] at hDet
  exact zero_ne_one hDet

lemma mapsTo_ball_of_equiv_fixes_exterior
    (Phi : R3 ≃ R3) (hFix : ∀ x : R3, 1 ≤ ‖x‖ → Phi x = x)
    (r : ℝ) (hr : 1 < r) : MapsTo Phi (ball (0 : R3) r) (ball (0 : R3) r) := by
  intro x hx
  by_cases hSmall : ‖x‖ < 1
  · have hImage : ‖Phi x‖ < 1 := by
      by_contra hNot
      have hFixedImage := hFix (Phi x) (le_of_not_gt hNot)
      have hFixed : Phi x = x := Phi.injective hFixedImage
      rw [hFixed] at hNot
      exact hNot hSmall
    exact mem_ball_zero_iff.mpr (hImage.trans hr)
  · rw [hFix x (le_of_not_gt hSmall)]
    exact hx

lemma notMem_fixedExteriorSource_closedBall_of_mem_ball_five_fourths
    (x : R3) (hx : x ∈ ball (0 : R3) (5/4 : ℝ)) :
    x ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) := by
  intro hSource
  have hDist : ‖fixedExteriorSourceCenter - x‖ ≤ (1/8 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hSource
  have hTriangle := norm_le_norm_sub_add fixedExteriorSourceCenter x
  rw [norm_fixedExteriorSourceCenter] at hTriangle
  have hNorm := mem_ball_zero_iff.mp hx
  linarith

theorem isAdmissibleMetric_pullbackMetric_of_smooth_equiv_fixes_exterior
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (Phi : R3 ≃ R3) (hPhi : ContDiff ℝ ∞ (Phi : R3 → R3))
    (hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3))
    (hFix : ∀ x : R3, 1 ≤ ‖x‖ → Phi x = x) :
    IsAdmissibleMetric (pullbackMetric g (Phi : R3 → R3)) := by
  let k : MatrixField := pullbackMetric g (Phi : R3 → R3)
  have hSmooth : ContDiff ℝ ∞ k := by
    exact contDiffOn_univ.mp
      (contDiffOn_native_source_chart_pullbackMetric g hg (Phi : R3 → R3)
        univ isOpen_univ hPhi.contDiffOn)
  have hOpen : IsOpen {y : R3 | 1 < ‖y‖} :=
    isOpen_lt continuous_const continuous_norm
  have hExterior : EqOn k (fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      {y : R3 | 1 < ‖y‖} := by
    intro x hx
    have hNear : (Phi : R3 → R3) =ᶠ[𝓝 x] (id : R3 → R3) := by
      filter_upwards [hOpen.mem_nhds hx] with y hy
      exact hFix y hy.le
    dsimp only [k]
    rw [pullbackMetric_eq_original_D,
      D_eq_of_eventuallyEq _ id x hNear, D_id, hFix x hx.le,
      hg.euclidean_exterior x hx.le]
    simp
  refine { smooth := ?_, posDef := ?_, euclidean_exterior := ?_ }
  · intro i j
    exact contDiff_pi.mp (contDiff_pi.mp hSmooth i) j
  · intro x
    exact pullbackMetric_posDef_of_injective_fderiv g hg (Phi : R3 → R3) x
      (injective_fderiv_of_smooth_equiv Phi hPhi hInv x)
  · intro x hx
    apply hExterior.closure hSmooth.continuous continuous_const
    have hSet : {y : R3 | 1 < ‖y‖} = (closedBall (0 : R3) 1)ᶜ := by
      ext y
      simp only [mem_setOf_eq, mem_compl_iff, mem_closedBall_zero_iff, not_le]
    rw [hSet, closure_compl, interior_closedBall (0 : R3) one_ne_zero]
    exact fun h => (not_lt_of_ge hx) (mem_ball_zero_iff.mp h)

theorem nativeMetricDifferential_pullback_source_eq_zero_of_source_match
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (Phi : R3 ≃ R3) (hPhi : ContDiff ℝ ∞ (Phi : R3 → R3))
    (hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3))
    (hFix : ∀ x : R3, 1 ≤ ‖x‖ → Phi x = x)
    (hMatch : ∀ x ∈ (radiusTwoOpens : Set R3),
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s x =
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (Phi x))
    (s : 𝓓(fixedExteriorSourceOpens, ℝ)) (x : R3)
    (hx : x ∈ ball (0 : R3) (5/4 : ℝ)) :
    nativeMetricDifferential (pullbackMetric g1 (Phi : R3 → R3))
      (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s) x = 0 := by
  let u1 : R3 → ℝ := radiusTwoSmoothSourceResponse
    fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s
  let u2 : R3 → ℝ := radiusTwoSmoothSourceResponse
    fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s
  let k : MatrixField := pullbackMetric g1 (Phi : R3 → R3)
  have hImage : Phi x ∈ ball (0 : R3) (5/4 : ℝ) :=
    mapsTo_ball_of_equiv_fixes_exterior Phi hFix (5/4 : ℝ) (by norm_num) hx
  have hxU : x ∈ (radiusTwoOpens : Set R3) :=
    ball_subset_ball (by norm_num : (5/4 : ℝ) ≤ 2) hx
  have hImageU : Phi x ∈ (radiusTwoOpens : Set R3) :=
    ball_subset_ball (by norm_num : (5/4 : ℝ) ≤ 2) hImage
  have hOutside := notMem_fixedExteriorSource_closedBall_of_mem_ball_five_fourths (Phi x) hImage
  have hSourceZero : s (Phi x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hSupport
    exact hOutside (ball_subset_closedBall (s.tsupport_subset hSupport))
  have hNative : nativeMetricDifferential g1 u1 (Phi x) = 0 := by
    dsimp only [u1]
    rw [nativeMetricDifferential_radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (Phi x) hImageU]
    exact hSourceZero
  have hDiv : coordinateFluxDivergence (metricDivergenceFlux g1 u1) (Phi x) = 0 := by
    rw [nativeMetricDifferential_eq_neg_coordinateFluxDivergence] at hNative
    exact neg_eq_zero.mp hNative
  have hu1 : ContDiffOn ℝ ∞ u1 (radiusTwoOpens : Set R3) :=
    (radiusTwoSmoothSourceResponse_spec fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s).2.1
  have hJ : IsUnit (coordinateJacobianMatrix (Phi : R3 → R3) x).det :=
    isUnit_det_D_of_smooth_equiv Phi hPhi hInv x
  have hCov := coordinateFluxDivergence_pullbackMetric_of_contDiffOn
    g1 hg1.smooth hg1.posDef (Phi : R3 → R3) u1
    (ball (0 : R3) (5/4 : ℝ)) (radiusTwoOpens : Set R3)
    isOpen_ball radiusTwoOpens.isOpen hPhi.contDiffOn hu1 x hx hImageU hJ
  rw [hDiv, mul_zero] at hCov
  have hPull : nativeMetricDifferential k (u1 ∘ (Phi : R3 → R3)) x = 0 := by
    rw [nativeMetricDifferential_eq_neg_coordinateFluxDivergence]
    change -coordinateFluxDivergence
      (metricDivergenceFlux (pullbackMetric g1 (Phi : R3 → R3))
        (u1 ∘ (Phi : R3 → R3))) x = 0
    rw [hCov, neg_zero]
  have hNear : u2 =ᶠ[𝓝 x] u1 ∘ (Phi : R3 → R3) := by
    filter_upwards [radiusTwoOpens.isOpen.mem_nhds hxU] with y hy
    exact hMatch y hy s
  exact (nativeMetricDifferential_congr_of_eventuallyEq k u2
    (u1 ∘ (Phi : R3 → R3)) x hNear).trans hPull

def sourcePartnerPullbackPrincipalScalar (g1 g2 : MatrixField) (Phi : R3 ≃ R3) : R3 → ℝ :=
  fun x => principalCoefficient (pullbackMetric g1 (Phi : R3 → R3)) x 2 2 /
    principalCoefficient g2 x 2 2

theorem contDiff_sourcePartnerPullbackPrincipalScalar
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (Phi : R3 ≃ R3) (hPhi : ContDiff ℝ ∞ (Phi : R3 → R3))
    (hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3))
    (hFix : ∀ x : R3, 1 ≤ ‖x‖ → Phi x = x) :
    ContDiff ℝ ∞ (sourcePartnerPullbackPrincipalScalar g1 g2 Phi) := by
  have hk := isAdmissibleMetric_pullbackMetric_of_smooth_equiv_fixes_exterior g1 hg1 Phi hPhi hInv hFix
  exact (contDiff_principalCoefficient_entry _ hk 2 2).div
    (contDiff_principalCoefficient_entry g2 hg2 2 2)
    (fun x => ((principalCoefficient_posDef g2 hg2 x).diag_pos (i := (2 : Fin 3))).ne')

theorem sourcePartnerPullbackPrincipalScalar_pos
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (Phi : R3 ≃ R3) (hPhi : ContDiff ℝ ∞ (Phi : R3 → R3))
    (hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3))
    (hFix : ∀ x : R3, 1 ≤ ‖x‖ → Phi x = x) :
    ∀ x : R3, 0 < sourcePartnerPullbackPrincipalScalar g1 g2 Phi x := by
  have hk := isAdmissibleMetric_pullbackMetric_of_smooth_equiv_fixes_exterior g1 hg1 Phi hPhi hInv hFix
  intro x
  exact div_pos ((principalCoefficient_posDef _ hk x).diag_pos (i := (2 : Fin 3)))
    ((principalCoefficient_posDef g2 hg2 x).diag_pos (i := (2 : Fin 3)))

theorem principalCoefficient_pullback_eq_scalar_smul_of_source_match
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (Phi : R3 ≃ R3) (hPhi : ContDiff ℝ ∞ (Phi : R3 → R3))
    (hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3))
    (hFix : ∀ x : R3, 1 ≤ ‖x‖ → Phi x = x)
    (hMatch : ∀ x ∈ (radiusTwoOpens : Set R3),
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s x =
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (Phi x)) :
    ∀ x ∈ ball (0 : R3) (5/4 : ℝ),
      principalCoefficient (pullbackMetric g1 (Phi : R3 → R3)) x =
        sourcePartnerPullbackPrincipalScalar g1 g2 Phi x • principalCoefficient g2 x := by
  classical
  let k : MatrixField := pullbackMetric g1 (Phi : R3 → R3)
  have hk := isAdmissibleMetric_pullbackMetric_of_smooth_equiv_fixes_exterior g1 hg1 Phi hPhi hInv hFix
  intro x hx
  have hxU : x ∈ (radiusTwoOpens : Set R3) :=
    ball_subset_ball (by norm_num : (5/4 : ℝ) ≤ 2) hx
  have hSource := notMem_fixedExteriorSource_closedBall_of_mem_ball_five_fourths x hx
  obtain ⟨s, hs⟩ := exists_radiusTwoSmoothSource_zeroGradient_fiveHessians_of_proved_uniqueContinuation
    fixedDirichletRegularity fixedSobolevCalculus g2 hg2 x hxU hSource
  have hFive (j : Fin 5) :
      (∑ i : Fin 3, ∑ l : Fin 3, principalCoefficient k x i l *
        traceFreeHessianMatrix ((g2 x)⁻¹) j i l) = 0 := by
    let u : R3 → ℝ := radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g2 hg2 (s j)
    have hPDE : nativeMetricDifferential k u x = 0 :=
      nativeMetricDifferential_pullback_source_eq_zero_of_source_match
        g1 g2 hg1 hg2 Phi hPhi hInv hFix hMatch (s j) x hx
    have hu : ContDiffOn ℝ ∞ u (radiusTwoOpens : Set R3) :=
      (radiusTwoSmoothSourceResponse_spec fixedDirichletRegularity fixedSobolevCalculus g2 hg2 (s j)).2.1
    have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) (radiusTwoOpens : Set R3) :=
      hu.fderiv_of_isOpen (m := ∞) radiusTwoOpens.isOpen (by simp)
    have hD2 : DifferentiableAt ℝ (fderiv ℝ u) x :=
      (hDu.contDiffAt (radiusTwoOpens.isOpen.mem_nhds hxU)).differentiableAt (by simp)
    have hJet := (nativeMetricDifferential_eq_jetFunctional k hk u x hD2).symm.trans hPDE
    change nativeMetricJetFunctional k x
      (fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 (s j)) x)
      (fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse
        fixedDirichletRegularity fixedSobolevCalculus g2 hg2 (s j))) x) = 0 at hJet
    rw [(hs j).2.1, (hs j).2.2, nativeMetricJetFunctional_matrixJetBilinear] at hJet
    simpa only [coordinateJetDrift, ContinuousLinearMap.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, neg_eq_zero] using hJet
  have haSym (i j : Fin 3) : (g2 x)⁻¹ i j = (g2 x)⁻¹ j i := by
    simpa using ((hg2.posDef x).inv.isHermitian.apply j i)
  have hASym (i j : Fin 3) : principalCoefficient k x i j = principalCoefficient k x j i := by
    simpa using ((principalCoefficient_posDef k hk x).isHermitian.apply j i)
  have ha22 : (g2 x)⁻¹ (2 : Fin 3) (2 : Fin 3) ≠ 0 :=
    ((hg2.posDef x).inv.diag_pos (i := (2 : Fin 3))).ne'
  have hForm := eq_smul_of_traceFreeHessianMatrix_contraction_eq_zero
    ((g2 x)⁻¹) (principalCoefficient k x) haSym hASym ha22 hFive
  have hv : vol g2 x ≠ 0 := (vol_pos g2 hg2 x).ne'
  ext i j
  change principalCoefficient k x i j =
    (principalCoefficient k x 2 2 / (vol g2 x * (g2 x)⁻¹ 2 2)) *
      (vol g2 x * (g2 x)⁻¹ i j)
  calc
    principalCoefficient k x i j =
        (principalCoefficient k x 2 2 / (g2 x)⁻¹ 2 2) * (g2 x)⁻¹ i j :=
      congrFun (congrFun hForm i) j
    _ = (principalCoefficient k x 2 2 / (vol g2 x * (g2 x)⁻¹ 2 2)) *
        (vol g2 x * (g2 x)⁻¹ i j) := by
      field_simp [hv, ha22]
      <;> ring

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.fderiv_symm_comp_fderiv_of_smooth_equiv
#print axioms OAI.AnisotropicCalderon.ExteriorSource.injective_fderiv_of_smooth_equiv
#print axioms OAI.AnisotropicCalderon.ExteriorSource.isUnit_det_D_of_smooth_equiv
#print axioms OAI.AnisotropicCalderon.ExteriorSource.mapsTo_ball_of_equiv_fixes_exterior
#print axioms OAI.AnisotropicCalderon.ExteriorSource.notMem_fixedExteriorSource_closedBall_of_mem_ball_five_fourths
#print axioms OAI.AnisotropicCalderon.ExteriorSource.isAdmissibleMetric_pullbackMetric_of_smooth_equiv_fixes_exterior
#print axioms OAI.AnisotropicCalderon.ExteriorSource.nativeMetricDifferential_pullback_source_eq_zero_of_source_match
#print axioms OAI.AnisotropicCalderon.ExteriorSource.sourcePartnerPullbackPrincipalScalar
#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiff_sourcePartnerPullbackPrincipalScalar
#print axioms OAI.AnisotropicCalderon.ExteriorSource.sourcePartnerPullbackPrincipalScalar_pos
#print axioms OAI.AnisotropicCalderon.ExteriorSource.principalCoefficient_pullback_eq_scalar_smul_of_source_match
