import Calderon.ActualKnownPhaseSourceKernelIdentity
import Calderon.ActualTwoMetricSeparatelySmoothSourceKernels
import Calderon.ActualOriginalSourceResponseCoordinatePDE
import Calderon.LocalMetricPullbackDivergence

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Distributions Matrix.Norms.Elementwise Matrix
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError

theorem original_chart_matching_fields_of_known_isometry
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (K1 K2 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G1 G2 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData1 : IsRadiusTwoSeparatelySmoothInverseSourceKernel g1 hg1 K1 G1)
    (hData2 : IsRadiusTwoSeparatelySmoothInverseSourceKernel g2 hg2 K2 G2)
    (W : Set R3) (hW : IsOpen W) (hConnected : IsConnected W)
    (hWRoom : W ⊆ (radiusTwoOpens : Set R3))
    (hSource : (fixedExteriorSourceOpens : Set R3) ⊆ W)
    (Phi : R3 → R3) (hPhiRoom : ∀ x ∈ W, Phi x ∈ (radiusTwoOpens : Set R3))
    (hPhiSmooth : ContDiffOn ℝ ∞ Phi W) (hPhiInj : Set.InjOn Phi W)
    (hPhiJac : ∀ x ∈ W, IsUnit (coordinateJacobianMatrix Phi x).det)
    (hIso : EqOn (pullbackMetric g1 Phi) g2 W)
    (hFix : ∀ x ∈ (fixedExteriorSourceOpens : Set R3), Phi x = x)
    (hMatch : ∀ x ∈ W,
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus g2 hg2 x =
        radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus g1 hg1 (Phi x))
    (V : Set R3) (hV : IsOpen V) (Xi1 Xi2 : R3 → R3)
    (hXi2Smooth : ContDiffOn ℝ ∞ Xi2 V) (hXi2Inj : Set.InjOn Xi2 V)
    (hXi2W : Set.MapsTo Xi2 V W) (hXi1 : EqOn Xi1 (Phi ∘ Xi2) V) :
    ∃ hRoom1 : ∀ x ∈ V, Xi1 x ∈ (radiusTwoOpens : Set R3),
      ContDiffOn ℝ ∞ Xi1 V ∧
      EqOn (pullbackMetric g1 Xi1) (pullbackMetric g2 Xi2) V ∧
      (∀ x : R3, ∀ hx : x ∈ V, ∀ y : R3, ∀ hy : y ∈ V, x ≠ y →
        G1 ⟨Xi1 y,hRoom1 y hy⟩ (Xi1 x) =
          G2 ⟨Xi2 y,hWRoom (hXi2W hy)⟩ (Xi2 x)) ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ V,
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (Xi1 x) =
          radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s (Xi2 x) := by
  -- First chart room: Xi1 = Phi ∘ Xi2 on V and Phi carries the known region W into radius two.
  have hRoom1 : ∀ x ∈ V, Xi1 x ∈ (radiusTwoOpens : Set R3) := by
    intro x hx
    have hx1 : Xi1 x = Phi (Xi2 x) := hXi1 hx
    rw [hx1]
    exact hPhiRoom (Xi2 x) (hXi2W hx)
  have hSmooth1 : ContDiffOn ℝ ∞ Xi1 V :=
    (hPhiSmooth.comp hXi2Smooth hXi2W).congr (fun x hx => hXi1 hx)
  -- Raw pullback in matrices: (D X)ᵀ g(X z) (D X).
  have hExpand (g : MatrixField) (X : R3 → R3) (z : R3) :
      pullbackMetric g X z =
        (operatorMatrixMap (fderiv ℝ X z))ᵀ * (g (X z) * operatorMatrixMap (fderiv ℝ X z)) := by
    simp only [pullbackMetric, operatorMatrixMap_comp, operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField, Matrix.mul_assoc]
  -- Germ equality on the open set V, actual chain rule, and the known isometry at Xi2 x.
  have hMetric : EqOn (pullbackMetric g1 Xi1) (pullbackMetric g2 Xi2) V := by
    intro x hx
    have hx1 : Xi1 x = Phi (Xi2 x) := hXi1 hx
    have hGerm : Xi1 =ᶠ[𝓝 x] Phi ∘ Xi2 := Filter.eventuallyEq_of_mem (hV.mem_nhds hx) hXi1
    have hPhiD : DifferentiableAt ℝ Phi (Xi2 x) :=
      (hPhiSmooth.contDiffAt (hW.mem_nhds (hXi2W hx))).differentiableAt (by simp)
    have hXi2D : DifferentiableAt ℝ Xi2 x :=
      (hXi2Smooth.contDiffAt (hV.mem_nhds hx)).differentiableAt (by simp)
    have hDeriv : fderiv ℝ Xi1 x = (fderiv ℝ Phi (Xi2 x)).comp (fderiv ℝ Xi2 x) :=
      hGerm.fderiv_eq.trans (fderiv_comp (x := x) hPhiD hXi2D)
    have hG2 : g2 (Xi2 x) = pullbackMetric g1 Phi (Xi2 x) := (hIso (hXi2W hx)).symm
    rw [hExpand g1 Xi1 x, hExpand g2 Xi2 x, hDeriv, hx1, hG2, hExpand g1 Phi (Xi2 x),
      operatorMatrixMap_comp, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  -- SAME original kernel rows on the connected known region, with the metrics swapped.
  have hRows := eqOn_radiusTwoSourceKernel_rows_of_known_isometry_and_source_match
    fixedDirichletRegularity fixedSobolevCalculus g2 g1 hg2 hg1 K2 K1 G2 G1 hData2.1 hData1.1
    W hW hConnected hWRoom hSource Phi hPhiRoom hPhiSmooth hPhiInj hPhiJac hIso hFix hMatch
  refine ⟨hRoom1, hSmooth1, hMetric, ?_, ?_⟩
  · intro x hx y hy hxy
    have hOff : Xi2 x ≠ Xi2 y := fun h => hxy (hXi2Inj hx hy h)
    have hRow := hRows (Xi2 y) (hXi2W hy) (Xi2 x) (hXi2W hx) hOff
    have hPole : (⟨Xi1 y, hRoom1 y hy⟩ : (radiusTwoOpens : Set R3)) =
        ⟨Phi (Xi2 y), hPhiRoom (Xi2 y) (hXi2W hy)⟩ := Subtype.ext (hXi1 hy)
    have hx1 : Xi1 x = Phi (Xi2 x) := hXi1 hx
    rw [hPole, hx1]
    exact hRow.symm
  -- SAME original source responses from the physical evaluation-family matching at Xi2 x.
  · intro s x hx
    have hFamily := congrFun (hMatch (Xi2 x) (hXi2W hx)) s
    have hx1 : Xi1 x = Phi (Xi2 x) := hXi1 hx
    rw [hx1]
    exact hFamily.symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
