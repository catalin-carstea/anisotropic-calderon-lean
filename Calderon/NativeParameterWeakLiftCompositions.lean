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

lemma contDiffAt_nativeParameterInverseEnergyComp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (I : P → StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero)
    (R : P → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero) (p : P)
    (hI : ContDiffAt ℝ ∞ I p) (hR : ContDiffAt ℝ ∞ R p) :
    ContDiffAt ℝ ∞ (fun t => (I t).comp (R t)) p := by
  apply ContDiffAt.clm_comp
  · exact hI
  · exact hR

lemma contDiffAt_nativeParameterZeroInclusionComp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (T : P → BallH1 →L[ℝ] BallH1Zero) (p : P) (hT : ContDiffAt ℝ ∞ T p) :
    ContDiffAt ℝ ∞ (fun t =>
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp (T t)) p := by
  apply ContDiffAt.clm_comp
  · exact contDiffAt_const
  · exact hT

lemma contDiffAt_nativeParameterHalfAffinePostComp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (S : P → BallH1 →L[ℝ] BallH1) (P₀ : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1)
    (p : P) (hS : ContDiffAt ℝ ∞ S p) :
    ContDiffAt ℝ ∞ (fun t => ((ContinuousLinearMap.id ℝ BallH1)-(S t)).comp P₀) p := by
  have hProjection : ContDiffAt ℝ ∞ (fun t => (ContinuousLinearMap.id ℝ BallH1)-(S t)) p :=
    contDiffAt_const.sub hS
  exact hProjection.clm_comp contDiffAt_const

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeParameterInverseEnergyComp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeParameterZeroInclusionComp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeParameterHalfAffinePostComp
