import Calderon.RadiusTwoNormalizedCompactTestEquation

/-! EXPANSION.json precedes direct compact-test normalization of the actual source. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Distributions InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem isWeakSolutionDirichlet_radiusTwoSourceSolution_dilated
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : RadiusTwoL2) :
    TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ)
      ((4 : ℝ) • radiusTwoNativeL2Dilation f)
      (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f)) := by
  let g2 : MatrixField := enlargedBallNormalizedMetric g 2
  let u : BallH1Zero := radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f)
  have hg2 : IsAdmissibleMetric g2 := isAdmissibleMetric_radiusTwoNormalized g hg
  have hcoeff : MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (principalCoefficient g2 x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := memLp_metricEnergyIntegrand g2 hg2
  apply (TauCeti.PDE.isWeakSolutionDirichlet_iff_forall_testFunction hcoeff
    ((4 : ℝ) • radiusTwoNativeL2Dilation f) u).mpr
  intro φ
  exact radiusTwoSourceSolution_dilated_compactTest_equation g hg f φ

end OAI.AnisotropicCalderon.ExteriorSource
