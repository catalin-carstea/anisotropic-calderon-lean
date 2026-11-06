import Calderon.MixedKernelConstruction.MixedKernelMonotoneCurrentPair
import Calderon.MixedKernelConstruction.MixedKernelPositiveChartAgreement
import Calderon.MixedKernelConstruction.MixedKernelObservedOutputRooms
import Calderon.MixedKernelConstruction.MixedKernelCurrentCommonPair
import Calderon.MixedKernelConstruction.MixedKernelProductOpenUCP
import Calderon.MixedKernelConstruction.MixedKernelCenteredRooms
import Calderon.MixedKernelConstruction.MixedKernelFiniteInterpolation
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNearOne
import Calderon.MixedKernelConstruction.MixedKernelAnnulusGeometry
import Calderon.MixedKernelConstruction.MixedKernelKnownSideCompactBuffer
import Calderon.MixedKernelConstruction.MixedKernelActualSeparatorAnchors
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNeighborhood
import Calderon.MixedKernelConstruction.MixedKernelCompatibleGluing
import Calderon.MixedKernelConstruction.MixedKernelFullCrossAssembly
import Calderon.MixedKernelConstruction.MixedKernelFullSeriesSolution
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

/-- The original joint Hessian criterion actually extends the current product solution across
the surface, agreeing on its whole old-side overlap. All rooms and series are constructed. -/
theorem exists_product_solution_extension_of_product_hessian
    (S : KnownSideSourceData) (L lam : ℝ) (p1 p2 : R3)
    (U : Set (R3 × R3)) (hU : IsOpen U) (hpU : (p1,p2) ∈ U)
    (rho : R3 × R3 → ℝ) (hrho : ContDiffOn ℝ ∞ rho U) (hrho0 : rho (p1,p2) = 0)
    (hTest : ProductHessianStrictAt (fun x => S.g1 (lam • x))
      (fun y => S.g2 (lam • y)) p1 p2 rho)
    (F : R3 × R3 → ℝ)
    (hSol : ProductSolutionOn S L lam F {z | z ∈ U ∧ 0 < rho z}) :
    ∃ (V : Set (R3 × R3)) (G : R3 × R3 → ℝ), IsOpen V ∧ (p1,p2) ∈ V ∧ V ⊆ U ∧
      ProductSolutionOn S L lam G V ∧
      EqOn G F (V ∩ {z | z ∈ U ∧ 0 < rho z}) := by
  obtain ⟨D1,hD1,O1,hO1D1,T,hTD1,D2,O2,S2,K1i,K2i,γ1,γ2,hfacts,
      hO1conn,hO2conn,hO1T,hO2S,HB,HA,ι,w,μ,hser,
      ell2,e2,l,eps,R,heps,hl,hR,hO2def,hS2def,hDt,hmonotone⟩ :=
    current_common_pair_from_product_hessian_monotone S L lam p1 p2 U hU hpU rho hrho hrho0 hTest F hSol
  rcases hfacts with ⟨hD1o,hD1c,hO1,hp1,hOD1,hT,hTne,hTD,
    hD2,hD2c,hO2,hp2,hOD2,hS2,hS2ne,hSD2,
    hK1i,hK2i,hγ11,hγ12,hγ21,hγ22,
    K1,KT,J2,JS,eta,hK1,hKT,hJ2,hJS,hD1K1,hTKT,hKTD1,hD2J2,hS2JS,hJSD2,hKU,heta,hmargin⟩
  obtain ⟨M,g,t,hM,hae,hg,hmono,ht,hSum,hlim,hfin⟩ :=
    currentCrossSeries_actual_limit F S L lam D1 hD1 O1 hO1D1 T hTD1
      D2 O2 S2 w μ hser
  let G := currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ
  have hprod : ProductSolutionOn S L lam G (O1 ×ˢ O2) :=
    currentCrossKernel_productSolutionOn F S L lam D1 hD1 O1 hO1 hO1D1 T hTD1
      D2 O2 S2 hO2 hOD2 w μ hser t ht
  have hobs : K1 ×ˢ S2 ⊆ {z | z ∈ U ∧ 0 < rho z} := by
    intro z hz
    exact ⟨hKU ⟨hz.1,hD2J2 (hJSD2 (hS2JS hz.2))⟩,
      heta.trans_le (hmargin z (Or.inl ⟨hz.1,hS2JS hz.2⟩))⟩
  have hfirst : EqOn G F (O1 ×ˢ S2) :=
    currentCrossKernel_first_eqOn F S L lam _ hSol D1 hD1 K1 hK1 hD1K1
      O1 hO1 hO1D1 T hTD1 S2 hobs w μ hser.1
  have hboxU : O1 ×ˢ O2 ⊆ U :=
    fun z hz => hKU ⟨hD1K1 (hO1D1 hz.1),hD2J2 (hOD2 hz.2)⟩
  have hknown : O1 ×ˢ S2 ⊆ {z | z ∈ U ∧ 0 < rho z} :=
    fun z hz => hobs ⟨hD1K1 (hO1D1 hz.1),hz.2⟩
  have heq := eqOn_positive_chart_box_of_monotone S L lam e2 l eps R heps hl hR hDt
    O1 O2 S2 hO1 hO2 hS2 hO2def hS2def U hU rho hrho.continuousOn hboxU hknown
    hmonotone F G hSol hprod hfirst
  exact ⟨O1 ×ˢ O2,G,hO1.prod hO2,⟨hp1,hp2⟩,hboxU,hprod,heq⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
