import Calderon.UniformBoundedGainPullback
import Calderon.RadiusTwoNormalizedFixedOperatorH2Regularity
import Calderon.RadiusTwoNormalizedNativeSourceEquation
import Calderon.RadiusTwoNormalizedSourceNormBound

/-! EXPANSION.json and AUTHORITY-SUPPLEMENT.json precede this actual source H2 bound.
The pre-existing regularity proposition remains an explicit hypothesis. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_uniformly_bounded_normalizedH2_radiusTwoSource
    (hreg : FixedDirichletRegularity) (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : RadiusTwoL2, ∃ U : BallSobolev 2,
      TauCeti.Wkp.firstOrder 1 U =
        (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) : BallH1) ∧
      ‖U‖ ≤ C * ‖f‖ := by
  trace "PROOFENTER generic-pullback actual uniform H2 source bound"
  let P : BallSobolev 0 → BallH1Zero → Prop := fun f u =>
    TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ) f u
  let R : BallSobolev 2 → BallH1Zero → Prop := fun U u =>
    TauCeti.Wkp.firstOrder 1 U = (u : BallH1)
  have hGain := exists_radiusTwoNormalizedMetric_fixedOperator_H2_regularity hreg g hg
  trace "FIXED GAIN generic-pullback actual uniform H2 source bound"
  let B : RadiusTwoL2 → BallH1Zero := fun f =>
    radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f)
  let F : RadiusTwoL2 → BallSobolev 0 := fun f => (4 : ℝ) • radiusTwoNativeL2Dilation f
  let C : ℝ := 3 * ‖radiusTwoSourceSolutionL g hg‖ + 4
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
      (norm_nonneg (radiusTwoSourceSolutionL g hg))) (by norm_num : (0 : ℝ) ≤ 4)
  trace "CONSTANT NONNEG generic-pullback actual uniform H2 source bound"
  have hWeak : ∀ f : RadiusTwoL2, P (F f) (B f) := fun f =>
    isWeakSolutionDirichlet_radiusTwoSourceSolution_dilated g hg f
  trace "ACTUAL WEAK PATH generic-pullback actual uniform H2 source bound"
  have hSum : ∀ f : RadiusTwoL2, ‖B f‖ + ‖F f‖ ≤ C * ‖f‖ := fun f =>
    norm_radiusTwoNormalizedSource_and_forcing_le g hg f
  trace "ACTUAL NORM PATH generic-pullback actual uniform H2 source bound"
  exact exists_uniform_bound_of_bounded_gain_pullback P R hGain B F hWeak C hC hSum

end OAI.AnisotropicCalderon.ExteriorSource
