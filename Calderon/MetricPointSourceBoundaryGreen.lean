import Calderon.ActualMixedKernelGlobalSurfaceExtension
import Calderon.SmoothPositiveMetricCompactGreen
import Calderon.ActualMetricWronskianDivergence
import Calderon.ActualBallDivergenceFlux

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ExteriorSource EnergyBridge MetricVolume MetricOperator ConnectionError
  DirichletFamily.DriftBootstrap SphereHarmonic RadialTestIntegration HarmonicPolynomialGreen
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

private theorem metricGreen_exists_supported_extension
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

theorem metric_pointSource_unitSphere_green
    (g : MatrixField) (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j))
    (hp : ∀ x, (g x).PosDef) (k : R3 → ℝ)
    (hSmooth : ContDiffOn ℝ ∞ k (ball (0 : R3) 2 \ {0}))
    (hPDE : ∀ z ∈ ball (0 : R3) 2 \ {0},
      coordinateFluxDivergence (metricDivergenceFlux g k) z = 0)
    (hPoint : ∀ phi : 𝓓(radiusTwoOpens,ℝ),
      (∫ z in radiusTwoOpens, k z * metricCompactTestDensity g phi z
        ∂(volume : Measure R3)) = phi (0 : R3))
    (u : SmoothData)
    (hu : ∀ z ∈ ball (0 : R3) 1,
      coordinateFluxDivergence (metricDivergenceFlux g u.1) z = 0) :
    (∫ theta : UnitSphere, ⟪theta.val,metricWronskianFlux g u.1 k theta.val⟫_ℝ
      ∂surfaceMeasure) = u.1 (0 : R3) := by
  let A : Set R3 := closedBall (0 : R3) 1 \ ball (0 : R3) (1/8 : ℝ)
  let T : Set R3 := ball (0 : R3) 2 \ {0}
  have hA : IsCompact A := (isCompact_closedBall _ _).diff isOpen_ball
  have hT : IsOpen T := isOpen_ball.sdiff isClosed_singleton
  have hAT : A ⊆ T := by
    intro x hx
    refine ⟨closedBall_subset_ball (by norm_num) hx.1,?_⟩
    intro h
    have hx0 : x = 0 := mem_singleton_iff.mp h
    exact hx.2 (by simp [hx0])
  obtain ⟨M,hM,hMc,hMs,_,hNear⟩ :=
    metricGreen_exists_supported_extension A T hA hT hAT k hSmooth
  let m : 𝓓(radiusTwoOpens,ℝ) := ⟨M,hM,hMc,fun x hx => (hMs hx).1⟩
  have hMDensity : ∀ x ∈ A, metricCompactTestDensity g m x = 0 := by
    intro x hx
    change -coordinateFluxDivergence (metricDivergenceFlux g (m : R3 → ℝ)) x = 0
    have hCongr := coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
      g M k x (hNear x hx)
    change -coordinateFluxDivergence (metricDivergenceFlux g M) x = 0
    rw [hCongr,hPDE x (hAT hx),neg_zero]
  obtain ⟨chi,hChi,_,hChiSupport,hChiOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      (isOpen_ball : IsOpen (ball (0 : R3) 1))
      (isClosed_closedBall : IsClosed (closedBall (0 : R3) (1/4 : ℝ)))
      (closedBall_subset_ball (by norm_num : (1/4 : ℝ) < 1))
  have hPhiSupport : tsupport (fun x : R3 => chi x * u.1 x) ⊆ closedBall (0 : R3) 1 := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    have hc : chi x ≠ 0 := by
      intro h
      exact hx (by simp only [h,zero_mul])
    have hb : x ∈ ball (0 : R3) 1 := by
      rw [← hChiSupport]
      exact hc
    exact ball_subset_closedBall hb
  have hPhiCompact : HasCompactSupport (fun x : R3 => chi x * u.1 x) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hPhiSupport
  let phi : 𝓓(radiusTwoOpens,ℝ) :=
    ⟨fun x => chi x * u.1 x,hChi.mul u.2,hPhiCompact,
      fun x hx => closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) (hPhiSupport hx)⟩
  have hPhiZero : phi (0 : R3) = u.1 (0 : R3) := by
    have hc : chi (0 : R3) = 1 := (hChiOne 0).mp (by simp)
    change chi 0 * u.1 0 = u.1 0
    rw [hc,one_mul]
  have hPhiGerm : ∀ x ∈ ball (0 : R3) (1/4 : ℝ), (phi : R3 → ℝ) =ᶠ[𝓝 x] u.1 := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    have hc : chi z = 1 := (hChiOne z).mp (ball_subset_closedBall hz)
    change chi z * u.1 z = u.1 z
    rw [hc,one_mul]
  have hSourceReplace : (∫ x in radiusTwoOpens, k x *
      metricCompactTestDensity g phi x ∂(volume : Measure R3)) =
      ∫ x in radiusTwoOpens, M x *
        metricCompactTestDensity g phi x ∂(volume : Measure R3) := by
    apply setIntegral_congr_fun radiusTwoOpens.isOpen.measurableSet
    intro x hx
    dsimp only
    by_cases ha : x ∈ A
    · rw [(hNear x ha).eq_of_nhds]
    · have hd : metricCompactTestDensity g phi x = 0 := by
        by_cases hClosed : x ∈ closedBall (0 : R3) 1
        · have hSmall : x ∈ ball (0 : R3) (1/8 : ℝ) := by
            by_contra hn
            exact ha ⟨hClosed,hn⟩
          have hQuarter : x ∈ ball (0 : R3) (1/4 : ℝ) := ball_subset_ball (by norm_num) hSmall
          change -coordinateFluxDivergence (metricDivergenceFlux g (phi : R3 → ℝ)) x = 0
          rw [coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
            g (phi : R3 → ℝ) u.1 x (hPhiGerm x hQuarter),
            hu x (ball_subset_ball (by norm_num : (1/8 : ℝ) ≤ 1) hSmall),neg_zero]
        · exact metricCompactTestDensity_eq_zero_of_notMem_tsupport g phi x
            (fun h => hClosed (hPhiSupport h))
      rw [hd,mul_zero,mul_zero]
  have hRestrict : (∫ x in radiusTwoOpens, phi x *
      metricCompactTestDensity g m x ∂(volume : Measure R3)) =
      ∫ x in ball (0 : R3) 1, phi x *
        metricCompactTestDensity g m x ∂(volume : Measure R3) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero radiusTwoOpens.isOpen.measurableSet
      (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2))
    intro x hx
    have hc : chi x = 0 := by
      apply notMem_support.mp
      rw [hChiSupport]
      exact hx.2
    change chi x * u.1 x * _ = 0
    rw [hc,zero_mul,zero_mul]
  have hWeight : (∫ x in ball (0 : R3) 1, phi x *
      metricCompactTestDensity g m x ∂(volume : Measure R3)) =
      ∫ x in ball (0 : R3) 1, u.1 x *
        metricCompactTestDensity g m x ∂(volume : Measure R3) := by
    apply setIntegral_congr_fun isOpen_ball.measurableSet
    intro x hx
    dsimp only
    by_cases hQuarter : x ∈ closedBall (0 : R3) (1/4 : ℝ)
    · have hc : chi x = 1 := (hChiOne x).mp hQuarter
      change chi x * u.1 x * _ = u.1 x * _
      rw [hc,one_mul]
    · have ha : x ∈ A := by
        refine ⟨ball_subset_closedBall hx,?_⟩
        intro hs
        exact hQuarter (ball_subset_closedBall (ball_subset_ball (by norm_num) hs))
      rw [hMDensity x ha,mul_zero,mul_zero]
  let W : R3 → R3 := metricWronskianFlux g u.1 M
  have hW : ContDiff ℝ 1 W :=
    (contDiff_metricWronskianFlux g hs hp u.1 M u.2 hM).of_le (by simp)
  have hDiv : ∀ x ∈ ball (0 : R3) 1, coordinateFluxDivergence W x =
      u.1 x * metricCompactTestDensity g m x := by
    intro x hx
    rw [coordinateFluxDivergence_metricWronskianFlux g hs hp u.1 M u.2 hM x,
      hu x hx,mul_zero,zero_sub,
      metricCompactTestDensity]
    change -(u.1 x * coordinateFluxDivergence (metricDivergenceFlux g M) x) =
      u.1 x * (-coordinateFluxDivergence (metricDivergenceFlux g M) x)
    ring
  have hRadial : radialDivergence (EuclideanSpace.basisFun (Fin 3) ℝ) W =
      coordinateFluxDivergence W := by
    funext x
    rw [radialDivergence_euclidean_coordinates _ hW]
    rfl
  have hGauss := integral_unitBall_radialDivergence_eq_surfaceFlux
    (EuclideanSpace.basisFun (Fin 3) ℝ) W hW
  rw [hRadial] at hGauss
  have hBoundary : (∫ theta : UnitSphere, ⟪theta.val,W theta.val⟫_ℝ ∂surfaceMeasure) =
      ∫ theta : UnitSphere, ⟪theta.val,metricWronskianFlux g u.1 k theta.val⟫_ℝ ∂surfaceMeasure := by
    apply integral_congr_ae
    apply ae_of_all
    intro theta
    have ht : theta.val ∈ A := by
      refine ⟨?_,?_⟩
      · rw [mem_closedBall_zero_iff,norm_eq_of_mem_sphere theta]
      · rw [mem_ball_zero_iff,norm_eq_of_mem_sphere theta]
        norm_num
    have hn := hNear theta.val ht
    have hv := hn.eq_of_nhds
    have hg' := hn.gradient.eq_of_nhds
    change ⟪theta.val,metricWronskianFlux g u.1 M theta.val⟫_ℝ = _
    simp only [metricWronskianFlux,metricDivergenceFlux,hv,hg']
  symm
  calc
    u.1 0 = phi 0 := hPhiZero.symm
    _ = ∫ x in radiusTwoOpens, k x *
        metricCompactTestDensity g phi x ∂(volume : Measure R3) := (hPoint phi).symm
    _ = ∫ x in radiusTwoOpens, M x *
        metricCompactTestDensity g phi x ∂(volume : Measure R3) := hSourceReplace
    _ = ∫ x in radiusTwoOpens, phi x *
        metricCompactTestDensity g m x ∂(volume : Measure R3) :=
      smooth_positive_metric_compactTest_green_symmetry g hs hp phi m
    _ = ∫ x in ball (0 : R3) 1, phi x *
        metricCompactTestDensity g m x ∂(volume : Measure R3) := hRestrict
    _ = ∫ x in ball (0 : R3) 1, u.1 x *
        metricCompactTestDensity g m x ∂(volume : Measure R3) := hWeight
    _ = ∫ x in ball (0 : R3) 1, coordinateFluxDivergence W x ∂(volume : Measure R3) :=
      setIntegral_congr_fun isOpen_ball.measurableSet (fun x hx => (hDiv x hx).symm)
    _ = ∫ theta : UnitSphere, ⟪theta.val,W theta.val⟫_ℝ ∂surfaceMeasure := hGauss
    _ = _ := hBoundary

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
