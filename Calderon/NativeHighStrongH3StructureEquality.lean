import Calderon.NativeHighStrongSobolevTopology

/-! Equality of the full cached H3 structures, not only of their projections; no new
norm is introduced. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

attribute [local instance_reducible] highStrongNativeH3Group
attribute [local instance_reducible] highStrongNativeH3Space
attribute [local instance] highStrongNativeH3Group
attribute [local instance] highStrongNativeH3Space

lemma nativeHighStrongH3_normedAddCommGroup_eq_stage :
    highStrongNativeH3Group =
      (TauCeti.SobolevStage.instNormedAddCommGroup
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2 : NormedAddCommGroup (BallSobolev 3)) := rfl

lemma nativeHighStrongH3_normedSpace_eq_stage :
    @Eq (@NormedSpace ℝ (BallSobolev 3) Real.normedField
      (@NormedAddCommGroup.toSeminormedAddCommGroup (BallSobolev 3) highStrongNativeH3Group))
      highStrongNativeH3Space
      (TauCeti.SobolevStage.instNormedSpace
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2) := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongH3_normedAddCommGroup_eq_stage
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongH3_normedSpace_eq_stage
