import Calderon.NativeHighStrongSobolevTopology

/-! Before-source: weak-native-instance-repair-author-oct16-v001/
EXPANSION-native-high-h3-full-structure-equality-v092.md.
Full original cached H3 structures; no projected equality or new norm. -/
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
