import Calderon.NativeInvertibleWeakLiftTopology
import Calderon.ActualReferenceWeakHalfLift

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma contDiffAt_nativeZeroWeakFunctionalInverse_of_isInvertible
    (A : (ℝ × (R3 × ℝ)) → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (p : ℝ × (R3 × ℝ)) (hA : ContDiffAt ℝ ∞ A p) (hi : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => functionalInverse (A t)) p := by
  apply contDiffAt_functionalInverse_of_isInvertible
  · exact hA
  · exact hi

lemma contDiffAt_nativeHalfAffineLiftFormula
    (I : (ℝ × (R3 × ℝ)) → StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero)
    (R : (ℝ × (R3 × ℝ)) → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (hI : ContDiffAt ℝ ∞ I p) (hR : ContDiffAt ℝ ∞ R p) :
    ContDiffAt ℝ ∞ (fun t =>
      ((ContinuousLinearMap.id ℝ BallH1) -
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
          ((I t).comp (R t))).comp (harmonicFirstOrderLiftCompletion hF)) p := by
  have hIR : ContDiffAt ℝ ∞ (fun t => (I t).comp (R t)) p := by
    apply ContDiffAt.clm_comp
    · exact hI
    · exact hR
  have hJIR : ContDiffAt ℝ ∞ (fun t =>
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
        ((I t).comp (R t))) p := by
    apply ContDiffAt.clm_comp
    · exact contDiffAt_const
    · exact hIR
  have hProjection : ContDiffAt ℝ ∞ (fun t =>
      (ContinuousLinearMap.id ℝ BallH1) -
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
          ((I t).comp (R t))) p := by
    exact contDiffAt_const.sub hJIR
  exact hProjection.clm_comp contDiffAt_const

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeZeroWeakFunctionalInverse_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeHalfAffineLiftFormula
