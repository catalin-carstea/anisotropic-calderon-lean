import Calderon.RadiusTwoNormalizedSmoothForcing
import Calderon.RadiusTwoNormalizedNativeSourceEquation

/-! Full EXPANSION.json precedes the actual smooth-source weak equation, independently of hreg. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation radiusTwoNativeL2Dilation

run_cmd Lean.logInfo "BEFORE HEADER actual smooth-source W-s weak equation"

lemma radiusTwoNormalizedSmoothSource_order_weak_equation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (s : ℕ) (F : SmoothData) :
    TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (TauCeti.Wkp.value s (smoothBallSobolev s (radiusTwoNormalizedSmoothForcing F)))
      (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F))) := by
  trace "PROOFENTER actual smooth-source W-s weak equation"
  let u : BallH1Zero := radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F))
  have hValue := value_radiusTwoNormalizedSmoothForcing s F
  trace "FORCING VALUE MADE actual smooth-source W-s weak equation"
  have hSource := isWeakSolutionDirichlet_radiusTwoSourceSolution_dilated g hg (smoothRadiusTwoForcing F)
  trace "NATIVE SOURCE EQUATION MADE actual smooth-source W-s weak equation"
  have hWeak : TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (TauCeti.Wkp.value s (smoothBallSobolev s (radiusTwoNormalizedSmoothForcing F))) u :=
    Eq.mp (congrArg (fun h : BallSobolev 0 => TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ) h u) hValue.symm) hSource
  trace "FORCING TRANSPORT MADE actual smooth-source W-s weak equation"
  exact hWeak

run_cmd Lean.logInfo "AFTER DECLARATION actual smooth-source W-s weak equation"
end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedSmoothSource_order_weak_equation
