import Calderon.NativeParameterWeakLiftCompositions
import Calderon.NativeHarmonicH1LiftCompletion
import Calderon.NativeInvertibleWeakLiftTopology

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Expanded before source in EXPANSION-native-parameter-affine-lift-opaque-inverse-repair-v001.json. -/

attribute [local irreducible] harmonicFirstOrderLiftCompletion

lemma contDiffAt_nativeParameterHalfAffineLiftFormula
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (I : P → StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero)
    (R : P → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (hF : SphereFischerInner) (p : P)
    (hI : ContDiffAt ℝ ∞ I p) (hR : ContDiffAt ℝ ∞ R p) :
    ContDiffAt ℝ ∞ (fun t =>
      ((ContinuousLinearMap.id ℝ BallH1) -
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
          ((I t).comp (R t))).comp (harmonicFirstOrderLiftCompletion hF)) p := by
  have hIR := contDiffAt_nativeParameterInverseEnergyComp I R p hI hR
  have hJIR := contDiffAt_nativeParameterZeroInclusionComp (fun t => (I t).comp (R t)) p hIR
  exact contDiffAt_nativeParameterHalfAffinePostComp
    (fun t => (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
      ((I t).comp (R t))) (harmonicFirstOrderLiftCompletion hF) p hJIR

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeParameterHalfAffineLiftFormula
