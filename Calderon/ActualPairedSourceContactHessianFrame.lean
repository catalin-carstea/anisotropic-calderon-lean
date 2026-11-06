import Calderon.ActualSourceHarmonicChartCanonicalHessians
import Calderon.ActualRadiusTwoSourceSeparation
import Calderon.ActualSourceContactSourceFree
import Calderon.ActualSourceFrontierCovectorGram
import Calderon.DistinctSourceChartContactMetric
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Topology.NhdsWithin

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
open EnergyBridge DirichletFamily Literature MetricVolume MetricOperator ConnectionError
  MetricCompatibleSourceJetAlgebra

theorem exists_radiusTwoSource_commonChart_contact_hessian_frame
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g1 f = minimalEnergy g2 f)
    (W : Set R3) (hW : IsOpen W) (Phi : R3 → R3)
    (hMaps : ∀ y ∈ W, Phi y ∈ (radiusTwoOpens : Set R3))
    (hDiff : ∀ y ∈ W, DifferentiableAt ℝ Phi y)
    (hMatch : ∀ y ∈ W, ∀ f : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        g2 hg2 f y =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        g1 hg1 f (Phi y))
    (hMetric : ∀ y ∈ W, g2 y = (D Phi y)ᵀ * g1 (Phi y) * D Phi y)
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3))
    (hpW : p ∈ closure W) (hpUnit : ‖p‖ ≤ 1) :
    ∃ (q : R3) (c : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
      (s : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ))
      (e1 e2 : OpenPartialHomeomorph R3 R3) (r : ℝ) (V Z : Set R3),
      let u1 : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ :=
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1
      let u2 : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ :=
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2
      let G1 : MatrixField := pullbackMetric g1 e1.symm
      let G2 : MatrixField := pullbackMetric g2 e2.symm
      q ∈ (radiusTwoOpens : Set R3) ∧ ‖q‖ ≤ 1 ∧
      q ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) ∧
      p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) ∧
      Tendsto Phi (nhdsWithin p W) (nhds q) ∧
      (∀ f : 𝓓(fixedExteriorSourceOpens, ℝ), u1 f q = u2 f p) ∧
      (e1 : R3 → R3) = radiusTwoSourceEuclideanCoordinates
        fixedDirichletRegularity fixedSobolevCalculus g1 hg1 c ∧
      (e2 : R3 → R3) = radiusTwoSourceEuclideanCoordinates
        fixedDirichletRegularity fixedSobolevCalculus g2 hg2 c ∧
      q ∈ e1.source ∧ p ∈ e2.source ∧ e1 q = 0 ∧ e2 p = 0 ∧
      (0 : R3) ∈ e1.target ∧ (0 : R3) ∈ e2.target ∧
      e1.source ⊆ (radiusTwoOpens : Set R3) ∧
      e2.source ⊆ (radiusTwoOpens : Set R3) ∧
      ContDiffOn ℝ ∞ (e1 : R3 → R3) e1.source ∧
      ContDiffOn ℝ ∞ (e2 : R3 → R3) e2.source ∧
      ContDiffOn ℝ ∞ (e1.symm : R3 → R3) e1.target ∧
      ContDiffOn ℝ ∞ (e2.symm : R3 → R3) e2.target ∧
      HasFDerivAt (e1 : R3 → R3) (ContinuousLinearMap.id ℝ R3) q ∧
      HasFDerivAt (e1.symm : R3 → R3) (ContinuousLinearMap.id ℝ R3) 0 ∧
      (∀ z ∈ e1.target, IsUnit (coordinateJacobianMatrix e1.symm z).det) ∧
      (∀ z ∈ e2.target, IsUnit (coordinateJacobianMatrix e2.symm z).det) ∧
      (∀ i j : Fin 3, ContDiffOn ℝ ∞ (fun z => G1 z i j) e1.target) ∧
      (∀ i j : Fin 3, ContDiffOn ℝ ∞ (fun z => G2 z i j) e2.target) ∧
      (∀ z ∈ e1.target, (G1 z).PosDef) ∧
      (∀ z ∈ e2.target, (G2 z).PosDef) ∧
      (∀ z ∈ e1.target, e1.symm z ∉ (fixedExteriorSourceOpens : Set R3) →
        ∀ j : Fin 3, (∑ i : Fin 3,
          fderiv ℝ (fun y => principalCoefficient G1 y i j) z
            (EuclideanSpace.single i 1)) = 0) ∧
      (∀ z ∈ e2.target, e2.symm z ∉ (fixedExteriorSourceOpens : Set R3) →
        ∀ j : Fin 3, (∑ i : Fin 3,
          fderiv ℝ (fun y => principalCoefficient G2 y i j) z
            (EuclideanSpace.single i 1)) = 0) ∧
      (∀ f : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ z ∈ e1.target,
        e1.symm z ∉ (fixedExteriorSourceOpens : Set R3) →
        (∑ i : Fin 3, ∑ j : Fin 3, ((G1 z)⁻¹) i j *
          fderiv ℝ (fderiv ℝ ((u1 f) ∘ e1.symm)) z
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0) ∧
      (∀ f : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ z ∈ e2.target,
        e2.symm z ∉ (fixedExteriorSourceOpens : Set R3) →
        (∑ i : Fin 3, ∑ j : Fin 3, ((G2 z)⁻¹) i j *
          fderiv ℝ (fderiv ℝ ((u2 f) ∘ e2.symm)) z
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0) ∧
      G1 0 = g1 q ∧ G2 0 = G1 0 ∧
      0 < r ∧ ball (0 : R3) r ⊆ e1.target ∩ e2.target ∧
      (∀ z ∈ ball (0 : R3) r,
        e1.symm z ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) ∧
        e2.symm z ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) ∧
      IsOpen V ∧ p ∈ V ∧ V ⊆ e2.source ∧
      (∀ y ∈ V, e2 y ∈ ball (0 : R3) r) ∧
      (∀ y ∈ V ∩ W, Phi y = e1.symm (e2 y)) ∧
      Z = e2 '' (V ∩ W) ∧ IsOpen Z ∧
      Z ⊆ ball (0 : R3) r ∧ (0 : R3) ∈ closure Z ∧
      (∀ f : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ z ∈ Z,
        ((u1 f) ∘ e1.symm) z = ((u2 f) ∘ e2.symm) z) ∧
      ∀ k : Fin 5,
        u1 (s k) q = 0 ∧ fderiv ℝ (u1 (s k)) q = 0 ∧
        fderiv ℝ (fderiv ℝ (u1 (s k))) q =
          matrixJetBilinear (traceFreeHessianMatrix ((g1 q)⁻¹) k) ∧
        ((u1 (s k)) ∘ e1.symm) 0 = 0 ∧
        fderiv ℝ ((u1 (s k)) ∘ e1.symm) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ ((u1 (s k)) ∘ e1.symm)) 0 =
          matrixJetBilinear (traceFreeHessianMatrix ((g1 q)⁻¹) k) ∧
        ((u2 (s k)) ∘ e2.symm) 0 = 0 ∧
        fderiv ℝ ((u2 (s k)) ∘ e2.symm) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ ((u2 (s k)) ∘ e2.symm)) 0 =
          matrixJetBilinear (traceFreeHessianMatrix ((g1 q)⁻¹) k) := by
  classical
  let u1 := radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1
  let u2 := radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2
  let Psi : W → (radiusTwoOpens : Set R3) := fun y => ⟨Phi y, hMaps y y.property⟩
  have hFamily (y : W) :
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus
        g1 hg1 (Psi y : R3) =
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus
        g2 hg2 (y : R3) := by
    funext f
    exact (hMatch y y.property f).symm
  obtain ⟨qB, hContactFamily, hPsiLimit, hqNorm, hqFree, hpFree⟩ :=
    exists_radiusTwoSource_sourceFree_contact_and_tendsto
      fixedDirichletRegularity fixedSobolevCalculus Literature.radiusTwoSourceSeparation
      g1 g2 hg1 hg2 hΛ W Psi hFamily p hp hpW hpUnit
  let q : R3 := qB
  have hq : q ∈ (radiusTwoOpens : Set R3) := qB.property
  have hContact (f : 𝓓(fixedExteriorSourceOpens, ℝ)) : u1 f q = u2 f p :=
    congrFun hContactFamily f
  have hValLimit : Tendsto (Phi ∘ (Subtype.val : W → R3))
      (Filter.comap (Subtype.val : W → R3) (nhds p)) (nhds q) :=
    (continuous_subtype_val.tendsto qB).comp hPsiLimit
  have hMap : Filter.map (Subtype.val : W → R3)
      (Filter.comap (Subtype.val : W → R3) (nhds p)) = nhdsWithin p W := by
    exact Filter.map_comap_setCoe_val (nhds p) W
  have hLimit : Tendsto Phi (nhdsWithin p W) (nhds q) := by
    rw [← hMap]
    exact Filter.tendsto_map'_iff.mpr hValLimit
  obtain ⟨c, s, e1, he1, hqS, hE10, h0T1, hSub1, hFwd1, hInv1,
      hFD1, hIX1, hJac1, hGS1, hGP1, hCols1, hPDE1, hJets1⟩ :=
    exists_radiusTwoSource_harmonicChart_canonical_hessians g1 hg1 q hq hqFree
  have hCoord1 : coordinateJacobianMatrix (e1 : R3 → R3) q =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    change (fderiv ℝ (e1 : R3 → R3) q (coordinateVector j)) i = _
    rw [hFD1.fderiv]
    simp [coordinateVector, PiLp.single_apply, Matrix.one_apply, eq_comm]
  have hRank1 : (Matrix.of (fun i j => d (u1 (c i)) q j)).det ≠ 0 := by
    have hMatrix := coordinateJacobianMatrix_radiusTwoSourceEuclideanCoordinates
      g1 hg1 c q hq
    rw [← he1] at hMatrix
    have hOne : Matrix.of (fun i j => d (u1 (c i)) q j) =
        (1 : Matrix (Fin 3) (Fin 3) ℝ) := hMatrix.symm.trans hCoord1
    rw [hOne, Matrix.det_one]
    exact one_ne_zero
  have hRank2 := radiusTwoSourceCovectorMatrix_det_ne_zero_of_limit_match
    fixedDirichletRegularity fixedSobolevCalculus g1 hg1 g2 hg2 c Phi W hW p q
      hp hq hpW hLimit hMaps hDiff hMatch hMetric hRank1
  obtain ⟨e2, he2, hpS, hpF2T, hSub2, hFwdF2, hInv2, hJac2,
      hGS2, hGP2, hCols2, hPDE2⟩ :=
    exists_radiusTwoSourceEuclideanCoordinates_allSource_nondivergence
      fixedDirichletRegularity fixedSobolevCalculus g2 hg2 c p hp hRank2
  have hFwd2 : ContDiffOn ℝ ∞ (e2 : R3 → R3) e2.source := by
    rw [he2]
    exact hFwdF2
  have hCoordinateValues : radiusTwoSourceCoordinates
      fixedDirichletRegularity fixedSobolevCalculus g2 hg2 c p =
      radiusTwoSourceCoordinates fixedDirichletRegularity fixedSobolevCalculus
        g1 hg1 c q := by
    funext i
    exact (hContact (c i)).symm
  have hCoordinateSame := congrArg
    (fun v : Fin 3 → ℝ => (EuclideanSpace.equiv (Fin 3) ℝ).symm v) hCoordinateValues
  have hE20 : e2 p = 0 := by
    calc
      e2 p = e1 q := by
        simpa only [he1, he2, radiusTwoSourceEuclideanCoordinates] using hCoordinateSame
      _ = 0 := hE10
  have h0T2 : (0 : R3) ∈ e2.target := by
    simpa only [hE20] using e2.map_source hpS
  have hX10 : e1.symm (0 : R3) = q := by
    simpa only [hE10] using e1.left_inv hqS
  have hX20 : e2.symm (0 : R3) = p := by
    simpa only [hE20] using e2.left_inv hpS
  have hE2Diff : DifferentiableAt ℝ (e2 : R3 → R3) p :=
    (hFwd2.contDiffAt (e2.open_source.mem_nhds hpS)).differentiableAt (by simp)
  have hX2Diff : DifferentiableAt ℝ (e2.symm : R3 → R3) 0 :=
    (hInv2.contDiffAt (e2.open_target.mem_nhds h0T2)).differentiableAt (by simp)
  have hMetricContact := pullbackMetric_same_source_charts_eq_of_limit_match
    g1 g2 hg1 hg2 c Phi W hW p q hp hq hpW hLimit hMaps hDiff hMatch hMetric
    e1 e2 he1 he2 hqS hpS hFD1.differentiableAt hE2Diff
    (by simpa only [hE10] using hIX1.differentiableAt)
    (by simpa only [hE20] using hX2Diff)
  have hGContact : pullbackMetric g2 e2.symm 0 = pullbackMetric g1 e1.symm 0 := by
    simpa only [hE10] using hMetricContact
  have hG10 : pullbackMetric g1 e1.symm 0 = g1 q := by
    simp only [pullbackMetric, hX10, hIX1.fderiv, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
      operatorMatrixMap_metricOperatorField]
  let S : Set R3 := (closedBall fixedExteriorSourceCenter (1/8 : ℝ))ᶜ
  let R1 : Set R3 := e1.target ∩ (e1.symm : R3 → R3) ⁻¹' S
  let R2 : Set R3 := e2.target ∩ (e2.symm : R3 → R3) ⁻¹' S
  have hR1 : IsOpen R1 := hInv1.continuousOn.isOpen_inter_preimage
    e1.open_target isClosed_closedBall.isOpen_compl
  have hR2 : IsOpen R2 := hInv2.continuousOn.isOpen_inter_preimage
    e2.open_target isClosed_closedBall.isOpen_compl
  have h0R1 : (0 : R3) ∈ R1 := by
    refine ⟨h0T1, ?_⟩
    change e1.symm (0 : R3) ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)
    simpa only [hX10] using hqFree
  have h0R2 : (0 : R3) ∈ R2 := by
    refine ⟨h0T2, ?_⟩
    change e2.symm (0 : R3) ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)
    simpa only [hX20] using hpFree
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp ((hR1.inter hR2).mem_nhds ⟨h0R1,h0R2⟩)
  have hBallTargets : ball (0 : R3) r ⊆ e1.target ∩ e2.target :=
    fun z hz => ⟨(hBall hz).1.1, (hBall hz).2.1⟩
  have hBallFree (z : R3) (hz : z ∈ ball (0 : R3) r) :
      e1.symm z ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) ∧
      e2.symm z ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) :=
    ⟨(hBall hz).1.2, (hBall hz).2.2⟩
  have hNear : {y : R3 | Phi y ∈ e1.source} ∈ nhdsWithin p W :=
    hLimit (e1.open_source.mem_nhds hqS)
  obtain ⟨T, hT, hpT, hTW⟩ := mem_nhdsWithin.mp hNear
  let V : Set R3 := T ∩ (e2.source ∩ (e2 : R3 → R3) ⁻¹' ball (0 : R3) r)
  have hV : IsOpen V := hT.inter (e2.isOpen_inter_preimage isOpen_ball)
  have hpV : p ∈ V := by
    refine ⟨hpT, hpS, ?_⟩
    change e2 p ∈ ball (0 : R3) r
    simpa only [hE20, mem_ball, dist_self] using hr
  have hVS : V ⊆ e2.source := fun y hy => hy.2.1
  have hVBall (y : R3) (hy : y ∈ V) : e2 y ∈ ball (0 : R3) r := hy.2.2
  have hPoint (y : R3) (hy : y ∈ W) : e2 y = e1 (Phi y) := by
    have hValues : radiusTwoSourceCoordinates fixedDirichletRegularity fixedSobolevCalculus
        g2 hg2 c y = radiusTwoSourceCoordinates fixedDirichletRegularity fixedSobolevCalculus
        g1 hg1 c (Phi y) := by
      funext i
      exact hMatch y hy (c i)
    simpa only [he1, he2, radiusTwoSourceEuclideanCoordinates] using congrArg
      (fun v : Fin 3 → ℝ => (EuclideanSpace.equiv (Fin 3) ℝ).symm v) hValues
  have hBranch (y : R3) (hy : y ∈ V ∩ W) : Phi y = e1.symm (e2 y) := by
    rw [hPoint y hy.2]
    exact (e1.left_inv (hTW ⟨hy.1.1, hy.2⟩)).symm
  let Z : Set R3 := e2 '' (V ∩ W)
  have hZ : IsOpen Z := e2.isOpen_image_of_subset_source (hV.inter hW)
    (fun y hy => hVS hy.1)
  have hZBall : Z ⊆ ball (0 : R3) r := by
    rintro z ⟨y, hy, rfl⟩
    exact hVBall y hy.1
  have hpClosure : p ∈ closure (V ∩ W) := by
    apply mem_closure_iff_nhdsWithin_neBot.mpr
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hpV))]
    exact mem_closure_iff_nhdsWithin_neBot.mp hpW
  have hE2Cont : ContinuousAt (e2 : R3 → R3) p :=
    hFwd2.continuousOn.continuousAt (e2.open_source.mem_nhds hpS)
  have h0Z : (0 : R3) ∈ closure Z := by
    simpa only [hE20] using mem_closure_image hE2Cont hpClosure
  have hSourceEqual (f : 𝓓(fixedExteriorSourceOpens, ℝ)) (z : R3) (hz : z ∈ Z) :
      ((u1 f) ∘ e1.symm) z = ((u2 f) ∘ e2.symm) z := by
    obtain ⟨y, hy, rfl⟩ := hz
    change u1 f (e1.symm (e2 y)) = u2 f (e2.symm (e2 y))
    rw [e2.left_inv (hVS hy.1), ← hBranch y hy]
    exact (hMatch y hy.2 f).symm
  have hJetsEqual (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
      ((u1 f) ∘ e1.symm) 0 = ((u2 f) ∘ e2.symm) 0 ∧
      fderiv ℝ ((u1 f) ∘ e1.symm) 0 = fderiv ℝ ((u2 f) ∘ e2.symm) 0 ∧
      fderiv ℝ (fderiv ℝ ((u1 f) ∘ e1.symm)) 0 =
        fderiv ℝ (fderiv ℝ ((u2 f) ∘ e2.symm)) 0 := by
    let v1 : R3 → ℝ := (u1 f) ∘ e1.symm
    let v2 : R3 → ℝ := (u2 f) ∘ e2.symm
    have hu1 : ContDiffOn ℝ ∞ (u1 f) (radiusTwoOpens : Set R3) :=
      (radiusTwoSmoothSourceResponse_spec fixedDirichletRegularity fixedSobolevCalculus
        g1 hg1 f).2.1
    have hu2 : ContDiffOn ℝ ∞ (u2 f) (radiusTwoOpens : Set R3) :=
      (radiusTwoSmoothSourceResponse_spec fixedDirichletRegularity fixedSobolevCalculus
        g2 hg2 f).2.1
    have hv1 : ContDiffOn ℝ ∞ v1 (ball (0 : R3) r) :=
      (hu1.comp hInv1 (fun z hz => hSub1 (e1.map_target hz))).mono
        (fun z hz => (hBallTargets hz).1)
    have hv2 : ContDiffOn ℝ ∞ v2 (ball (0 : R3) r) :=
      (hu2.comp hInv2 (fun z hz => hSub2 (e2.map_target hz))).mono
        (fun z hz => (hBallTargets hz).2)
    have hvD1 : ContDiffOn ℝ ∞ (fderiv ℝ v1) (ball (0 : R3) r) :=
      hv1.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) isOpen_ball (by simp)
    have hvD2 : ContDiffOn ℝ ∞ (fderiv ℝ v2) (ball (0 : R3) r) :=
      hv2.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) isOpen_ball (by simp)
    have hvDD1 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ v1)) (ball (0 : R3) r) :=
      hvD1.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) isOpen_ball (by simp)
    have hvDD2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ v2)) (ball (0 : R3) r) :=
      hvD2.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) isOpen_ball (by simp)
    have hGerm (z : R3) (hz : z ∈ Z) : v1 =ᶠ[nhds z] v2 := by
      filter_upwards [hZ.mem_nhds hz] with y hy
      exact hSourceEqual f y hy
    have hEqD (z : R3) (hz : z ∈ Z) : fderiv ℝ v1 z = fderiv ℝ v2 z :=
      (hGerm z hz).fderiv_eq (𝕜 := ℝ)
    have hEqDD (z : R3) (hz : z ∈ Z) :
        fderiv ℝ (fderiv ℝ v1) z = fderiv ℝ (fderiv ℝ v2) z :=
      ((hGerm z hz).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    letI : NeBot (nhdsWithin (0 : R3) Z) := mem_closure_iff_nhdsWithin_neBot.mp h0Z
    have h0Ball : (0 : R3) ∈ ball (0 : R3) r := by
      simpa only [mem_ball, dist_self] using hr
    have hEqV : v1 =ᶠ[nhdsWithin (0 : R3) Z] v2 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hSourceEqual f z hz
    have hEqDV : (fderiv ℝ v1) =ᶠ[nhdsWithin (0 : R3) Z] (fderiv ℝ v2) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hEqD z hz
    have hEqDDV : (fderiv ℝ (fderiv ℝ v1)) =ᶠ[nhdsWithin (0 : R3) Z]
        (fderiv ℝ (fderiv ℝ v2)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hEqDD z hz
    exact ⟨tendsto_nhds_unique_of_eventuallyEq
      ((hv1.continuousOn.continuousAt (isOpen_ball.mem_nhds h0Ball)).mono_left nhdsWithin_le_nhds)
      ((hv2.continuousOn.continuousAt (isOpen_ball.mem_nhds h0Ball)).mono_left nhdsWithin_le_nhds) hEqV,
      tendsto_nhds_unique_of_eventuallyEq
      ((hvD1.continuousOn.continuousAt (isOpen_ball.mem_nhds h0Ball)).mono_left nhdsWithin_le_nhds)
      ((hvD2.continuousOn.continuousAt (isOpen_ball.mem_nhds h0Ball)).mono_left nhdsWithin_le_nhds) hEqDV,
      tendsto_nhds_unique_of_eventuallyEq
      ((hvDD1.continuousOn.continuousAt (isOpen_ball.mem_nhds h0Ball)).mono_left nhdsWithin_le_nhds)
      ((hvDD2.continuousOn.continuousAt (isOpen_ball.mem_nhds h0Ball)).mono_left nhdsWithin_le_nhds) hEqDDV⟩
  refine ⟨q, c, s, e1, e2, r, V, Z, ?_⟩
  change q ∈ (radiusTwoOpens : Set R3) ∧ _
  refine ⟨hq, hqNorm, hqFree, hpFree, hLimit, hContact, he1, he2, hqS, hpS,
    hE10, hE20, h0T1, h0T2, hSub1, hSub2, hFwd1, hFwd2, hInv1, hInv2,
    hFD1, hIX1, hJac1, hJac2, hGS1, hGS2, hGP1, hGP2, hCols1, hCols2,
    hPDE1, hPDE2, hG10, hGContact, hr, hBallTargets, hBallFree,
    hV, hpV, hVS, hVBall, hBranch, rfl, hZ, hZBall, h0Z, hSourceEqual, ?_⟩
  intro k
  obtain ⟨hPhysical0, hPhysical1, hPhysical2, hChart0, hChart1, hChart2⟩ := hJets1 k
  obtain ⟨hEqual0, hEqual1, hEqual2⟩ := hJetsEqual (s k)
  exact ⟨hPhysical0, hPhysical1, hPhysical2, hChart0, hChart1, hChart2,
    hEqual0.symm.trans hChart0, hEqual1.symm.trans hChart1, hEqual2.symm.trans hChart2⟩

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame

#print axioms OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame.exists_radiusTwoSource_commonChart_contact_hessian_frame
