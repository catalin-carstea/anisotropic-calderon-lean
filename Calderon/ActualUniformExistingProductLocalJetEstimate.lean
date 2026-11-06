import Calderon.ActualUniformProductExtensionJetBudget
import MixedKernelFullCrossExtension
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

theorem exists_uniform_existing_product_solution_local_jet_estimate
    (S:KnownSideSourceData) (p1 p2:R3) (U:Set (R3×R3)) (hU:IsOpen U) (hpU:(p1,p2)∈U)
    (rho:R3×R3→ℝ) (hrho:ContDiffOn ℝ ∞ rho U) (hrho0:rho (p1,p2)=0)
    (hTest:ProductHessianStrictAt (fun x => S.g1 ((0:ℝ) • x))
      (fun y => S.g2 ((0:ℝ) • y)) p1 p2 rho) :
    ∃ lambda0 r:ℝ,0 < lambda0 ∧ 0 < r ∧ ∃ Ksource:Set (R3×R3),
      IsCompact Ksource ∧ Ksource⊆{z | z∈U ∧ 0 < rho z} ∧ ball (p1,p2) r⊆U ∧
      ∃ C:ℕ→ℝ,(∀ n,0 < C n) ∧
      ∀ L:ℝ,∀ lambda∈Icc (0:ℝ) lambda0,∀ F:R3×R3→ℝ,ProductSolutionOn S L lambda F U →
      ∀ M:ℝ,0 ≤ M → (∀ z∈Ksource,‖F z‖ ≤ M) →
      ∀ n:ℕ,∀ z∈ball (p1,p2) r,‖iteratedFDeriv ℝ n F z‖ ≤ C n*M := by
  obtain ⟨lambda0,r,hlambda0,hr,Ksource,Vbig,hKsource,hKsourcePos,hVbig,hpVbig,hVbigU,hSmallV,
    C,hC,H⟩ := exists_uniform_product_extension_with_compact_cross_jet_budget S p1 p2 U hU hpU rho hrho hrho0 hTest
  let O1:=ball p1 r
  let O2:=ball p2 r
  have hO1:IsOpen O1 := isOpen_ball
  have hO2:IsOpen O2 := isOpen_ball
  have hp1:p1∈O1 := mem_ball_self hr
  have hp2:p2∈O2 := mem_ball_self hr
  have hc1:IsConnected O1 := (convex_ball p1 r).isConnected (nonempty_ball.mpr hr)
  have hc2:IsConnected O2 := (convex_ball p2 r).isConnected (nonempty_ball.mpr hr)
  have hOVBall:O1×ˢO2⊆ball (p1,p2) r := by
    intro z hz
    rw [mem_ball,Prod.dist_eq]
    exact max_lt (mem_ball.mp hz.1) (mem_ball.mp hz.2)
  have hBallOV:ball (p1,p2) r⊆O1×ˢO2 := by
    intro z hz
    exact ⟨(max_lt_iff.mp (show max (dist z.1 p1) (dist z.2 p2)<r from hz)).1,
      (max_lt_iff.mp (show max (dist z.1 p1) (dist z.2 p2)<r from hz)).2⟩
  have hOV:O1×ˢO2⊆Vbig := hOVBall.trans hSmallV
  have hOU:O1×ˢO2⊆U := hOV.trans hVbigU
  obtain ⟨he1,he2,-⟩ := hTest
  obtain ⟨T1,T2,C1,C2,hT1o,hT1n,hT1,hT2o,hT2n,hT2,hC1o,hpC1,hC1,hC2o,hpC2,hC2,hpos1,hpos2⟩ :=
    exists_positive_product_strips rho p1 p2 O1 O2 hO1 hO2 hp1 hp2 (hrho.mono hOU) hrho0 he1 he2
  refine ⟨lambda0,r,hlambda0,hr,Ksource,hKsource,hKsourcePos,hSmallV.trans hVbigU,C,hC,?_⟩
  intro L lambda hlam F hF M hM hBound
  have hFpositive:ProductSolutionOn S L lambda F {z | z∈U ∧ 0 < rho z} :=
    productSolutionOn_mono hF (fun z hz => hz.1)
  obtain ⟨G,hG,hGF,hJets⟩ := H L lambda hlam F hFpositive M hM hBound
  have hGP:ProductSolutionOn S L lambda G (O1×ˢO2) := productSolutionOn_mono hG hOV
  have hFP:ProductSolutionOn S L lambda F (O1×ˢO2) := productSolutionOn_mono hF hOU
  have hEq:=native_product_eq_of_eq_on_box S L lambda hO1 hc1 hO2 hc2 hGP hFP
    hT1o hT1n hT1 hC2o ⟨p2,hpC2⟩ hC2
    (fun x hx y hy => hGF ⟨hOV ⟨hT1 hx,hC2 hy⟩,hOU ⟨hT1 hx,hC2 hy⟩,hpos1 (x,y) ⟨hx,hy⟩⟩)
  intro n z hz
  have hGerm:G=ᶠ[𝓝 z] F := Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw =>
    hEq w.1 (hBallOV hw).1 w.2 (hBallOV hw).2
  have hDeriv:iteratedFDeriv ℝ n G z=iteratedFDeriv ℝ n F z := (hGerm.iteratedFDeriv ℝ n).eq_of_nhds
  rw [← hDeriv]
  exact hJets n z hz

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
