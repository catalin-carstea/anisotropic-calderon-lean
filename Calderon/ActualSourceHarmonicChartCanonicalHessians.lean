import Calderon.ActualFlattenedCanonicalSourceMenu
import Calderon.ActualSourceChartNondivergenceEquation
import Calderon.NativeSourceChartInverseConditioning
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Distributions Matrix BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
open EnergyBridge DirichletFamily Literature MetricVolume MetricCompatibleSourceJetAlgebra
  ConnectionError MetricOperator

theorem exists_radiusTwoSource_harmonicChart_canonical_hessians
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ (c : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
      (s : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ))
      (e : OpenPartialHomeomorph R3 R3),
      (e : R3 → R3) = radiusTwoSourceEuclideanCoordinates
        fixedDirichletRegularity fixedSobolevCalculus g hg c ∧
      p ∈ e.source ∧ e p = 0 ∧ (0 : R3) ∈ e.target ∧
      e.source ⊆ (radiusTwoOpens : Set R3) ∧
      ContDiffOn ℝ ∞ (e : R3 → R3) e.source ∧
      ContDiffOn ℝ ∞ (e.symm : R3 → R3) e.target ∧
      HasFDerivAt (e : R3 → R3) (ContinuousLinearMap.id ℝ R3) p ∧
      HasFDerivAt (e.symm : R3 → R3) (ContinuousLinearMap.id ℝ R3) 0 ∧
      (∀ z ∈ e.target, IsUnit (coordinateJacobianMatrix e.symm z).det) ∧
      (∀ i j : Fin 3, ContDiffOn ℝ ∞
        (fun z => pullbackMetric g e.symm z i j) e.target) ∧
      (∀ z ∈ e.target, (pullbackMetric g e.symm z).PosDef) ∧
      (∀ z ∈ e.target, e.symm z ∉ (fixedExteriorSourceOpens : Set R3) →
        ∀ j : Fin 3, (∑ i : Fin 3,
          fderiv ℝ (fun y => principalCoefficient (pullbackMetric g e.symm) y i j) z
            (EuclideanSpace.single i 1)) = 0) ∧
      (∀ f : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ z ∈ e.target,
        e.symm z ∉ (fixedExteriorSourceOpens : Set R3) →
        (∑ i : Fin 3, ∑ j : Fin 3, ((pullbackMetric g e.symm z)⁻¹) i j *
          fderiv ℝ (fderiv ℝ ((radiusTwoSmoothSourceResponse
            fixedDirichletRegularity fixedSobolevCalculus g hg f) ∘ e.symm)) z
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0) ∧
      ∀ k : Fin 5,
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
          g hg (s k) p = 0 ∧
        fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
          g hg (s k)) p = 0 ∧
        fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse
          fixedDirichletRegularity fixedSobolevCalculus g hg (s k))) p =
            matrixJetBilinear (traceFreeHessianMatrix ((g p)⁻¹) k) ∧
        ((radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
          g hg (s k)) ∘ e.symm) 0 = 0 ∧
        fderiv ℝ ((radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
          g hg (s k)) ∘ e.symm) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ ((radiusTwoSmoothSourceResponse
          fixedDirichletRegularity fixedSobolevCalculus g hg (s k)) ∘ e.symm)) 0 =
            matrixJetBilinear (traceFreeHessianMatrix ((g p)⁻¹) k) := by
  classical
  obtain ⟨c, hc⟩ := FixedSourceWitnesses.exists_radiusTwoSmoothSource_coordinate_firstJets
    g hg p hp hSource
  have hCoordJet (i : Fin 3) :
      radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p (c i) =
        compatibleSourceJetBasis g p (Sum.inr (Sum.inl i)) := by
    exact Prod.ext (hc i).1 (Prod.ext (hc i).2.1 (hc i).2.2)
  obtain ⟨hF0, hF1⟩ := radiusTwoSourceEuclideanCoordinates_normalized_of_gradient_jets
    g hg c p hp hCoordJet
  let F : R3 → R3 := radiusTwoSourceEuclideanCoordinates
    fixedDirichletRegularity fixedSobolevCalculus g hg c
  have hMatrix : (Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g hg (c i)) p j)) =
        (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    change fderiv ℝ (radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g hg (c i)) p
        (EuclideanSpace.single j 1) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
    rw [(hc i).2.1]
    simp [EuclideanSpace.coe_proj, PiLp.single_apply, Matrix.one_apply, eq_comm]
  have hDet : (Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g hg (c i)) p j)).det ≠ 0 := by
    rw [hMatrix, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨s, hs⟩ := FixedSourceWitnesses.exists_radiusTwoSmoothSource_zeroGradient_fiveHessians
    g hg p hp hSource
  obtain ⟨e, he, hpSource, hpTarget, hSourceSub, hForward, hInverse,
      hJac, hBSmooth, hBPos, hColumns, hPDE⟩ :=
    exists_radiusTwoSourceEuclideanCoordinates_allSource_nondivergence
      fixedDirichletRegularity fixedSobolevCalculus g hg c p hp hDet
  have hE0 : e p = 0 := by
    rw [he]
    exact hF0
  have hTarget0 : (0 : R3) ∈ e.target := by
    simpa only [hE0] using e.map_source hpSource
  have hX0 : e.symm (0 : R3) = p := by
    simpa only [hE0] using e.left_inv hpSource
  have hE1 : HasFDerivAt (e : R3 → R3) (ContinuousLinearMap.id ℝ R3) p := by
    rw [he]
    exact hF1
  have hXDiff : DifferentiableAt ℝ (e.symm : R3 → R3) 0 :=
    (hInverse.contDiffAt (e.open_target.mem_nhds hTarget0)).differentiableAt (by simp)
  have hFAtX : HasFDerivAt F (ContinuousLinearMap.id ℝ R3) (e.symm 0) := by
    rw [hX0]
    exact hF1
  have hComp : (ContinuousLinearMap.id ℝ R3).comp
      (fderiv ℝ (e.symm : R3 → R3) 0) = ContinuousLinearMap.id ℝ R3 :=
    NativeSourceChartCalculus.comp_eq_id_of_same_chart_hasFDerivAt
      F e 0 hTarget0 he (ContinuousLinearMap.id ℝ R3)
      (fderiv ℝ (e.symm : R3 → R3) 0) hFAtX hXDiff.hasFDerivAt
  have hDX0 : fderiv ℝ (e.symm : R3 → R3) 0 = ContinuousLinearMap.id ℝ R3 := by
    simpa only [ContinuousLinearMap.id_comp] using hComp
  have hX1 : HasFDerivAt (e.symm : R3 → R3) (ContinuousLinearMap.id ℝ R3) 0 := by
    rw [← hDX0]
    exact hXDiff.hasFDerivAt
  refine ⟨c, s, e, he, hpSource, hE0, hTarget0, hSourceSub, ?_, hInverse,
    hE1, hX1, hJac, hBSmooth, hBPos, hColumns, hPDE, ?_⟩
  · rw [he]
    exact hForward
  · intro k
    let u : R3 → ℝ := radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g hg (s k)
    let X : R3 → R3 := e.symm
    have hu0 : u p = 0 := (hs k).1
    have hDu0 : fderiv ℝ u p = 0 := (hs k).2.1
    have hD2u : fderiv ℝ (fderiv ℝ u) p =
        matrixJetBilinear (traceFreeHessianMatrix ((g p)⁻¹) k) := (hs k).2.2
    have hXp : X 0 = p := hX0
    have hDX : fderiv ℝ X 0 = ContinuousLinearMap.id ℝ R3 := hDX0
    have hu : ContDiffOn ℝ ∞ u (radiusTwoOpens : Set R3) :=
      (radiusTwoSmoothSourceResponse_spec fixedDirichletRegularity fixedSobolevCalculus
        g hg (s k)).2.1
    have hX : ContDiffOn ℝ ∞ X e.target := hInverse
    have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) (radiusTwoOpens : Set R3) :=
      hu.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) radiusTwoOpens.isOpen (by simp)
    have hDXSmooth : ContDiffOn ℝ ∞ (fderiv ℝ X) e.target :=
      hX.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) e.open_target (by simp)
    have huAt : DifferentiableAt ℝ u p :=
      (hu.contDiffAt (radiusTwoOpens.isOpen.mem_nhds hp)).differentiableAt (by simp)
    have hDuAt : DifferentiableAt ℝ (fderiv ℝ u) p :=
      (hDu.contDiffAt (radiusTwoOpens.isOpen.mem_nhds hp)).differentiableAt (by simp)
    have hXAt : DifferentiableAt ℝ X 0 := hXDiff
    have hDXAt : DifferentiableAt ℝ (fderiv ℝ X) 0 :=
      (hDXSmooth.contDiffAt (e.open_target.mem_nhds hTarget0)).differentiableAt (by simp)
    have hFirst : fderiv ℝ (u ∘ X) 0 = 0 := by
      have hOuter : DifferentiableAt ℝ u (X 0) := by
        rw [hXp]
        exact huAt
      simpa only [hXp, hDu0, ContinuousLinearMap.zero_comp] using
        (fderiv_comp (0 : R3) hOuter hXAt)
    have hNear : fderiv ℝ (u ∘ X) =ᶠ[nhds (0 : R3)]
        (fun z : R3 => (fderiv ℝ u (X z)).comp (fderiv ℝ X z)) := by
      filter_upwards [e.open_target.mem_nhds hTarget0] with z hz
      have hXz : X z ∈ (radiusTwoOpens : Set R3) := hSourceSub (e.map_target hz)
      have huDz : DifferentiableAt ℝ u (X z) :=
        (hu.contDiffAt (radiusTwoOpens.isOpen.mem_nhds hXz)).differentiableAt (by simp)
      have hXDz : DifferentiableAt ℝ X z :=
        (hX.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp)
      exact fderiv_comp z huDz hXDz
    have hDuAtX : HasFDerivAt (fderiv ℝ u)
        (fderiv ℝ (fderiv ℝ u) p) (X 0) := by
      rw [hXp]
      exact hDuAt.hasFDerivAt
    have hC : HasFDerivAt (fun z : R3 => fderiv ℝ u (X z))
        ((fderiv ℝ (fderiv ℝ u) p).comp (fderiv ℝ X 0)) 0 := by
      simpa only [Function.comp_def] using hDuAtX.comp (0 : R3) hXAt.hasFDerivAt
    have hD : HasFDerivAt (fderiv ℝ X)
        (fderiv ℝ (fderiv ℝ X) 0) 0 := hDXAt.hasFDerivAt
    have hCD := hC.clm_comp hD
    have hSecond := hNear.fderiv_eq (𝕜 := ℝ)
    rw [hCD.fderiv] at hSecond
    have hFinal : fderiv ℝ (fderiv ℝ (u ∘ X)) 0 =
        matrixJetBilinear (traceFreeHessianMatrix ((g p)⁻¹) k) := by
      apply ContinuousLinearMap.ext
      intro U
      apply ContinuousLinearMap.ext
      intro V
      have hValue := congrArg
        (fun A : R3 →L[ℝ] (R3 →L[ℝ] ℝ) => A U V) hSecond
      simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
        hXp, hDu0, hDX, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.zero_apply, zero_add, hD2u] using hValue
    refine ⟨(hs k).1, (hs k).2.1, (hs k).2.2, ?_, hFirst, hFinal⟩
    change u (X 0) = 0
    rw [hXp]
    exact hu0

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame

#print axioms OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame.exists_radiusTwoSource_harmonicChart_canonical_hessians
