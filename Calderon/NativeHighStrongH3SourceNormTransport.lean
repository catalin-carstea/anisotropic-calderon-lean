import Calderon.NativeHighStrongH3StructureEquality
import Calderon.NormedSourceContinuousLinearMapTransport

/-! Full before-source: weak-native-instance-repair-author-oct16-v001/
EXPANSION-native-h3-full-source-norm-bridge-v127.md. SAME full chosen/Stage H3 source data and the exact canonical operator-norm transport; no native norm registration or trace premise. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic

def nativeHighStrongH3NormedSourceData :
    Σ G : NormedAddCommGroup (BallSobolev 3),
      @NormedSpace ℝ (BallSobolev 3) Real.normedField G.toSeminormedAddCommGroup :=
  ⟨highStrongNativeH3Group, highStrongNativeH3Space⟩

def nativeStageH3NormedSourceData :
    Σ G : NormedAddCommGroup (BallSobolev 3),
      @NormedSpace ℝ (BallSobolev 3) Real.normedField G.toSeminormedAddCommGroup :=
  ⟨TauCeti.SobolevStage.instNormedAddCommGroup
      (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
      (Omega := ballOpens) (p := 2) 2,
    TauCeti.SobolevStage.instNormedSpace
      (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
      (Omega := ballOpens) (p := 2) 2⟩

lemma nativeHighStrongH3NormedSourceData_eq_stage :
    nativeHighStrongH3NormedSourceData = nativeStageH3NormedSourceData := by
  exact Sigma.mk.inj_iff.mpr
    ⟨nativeHighStrongH3_normedAddCommGroup_eq_stage,
      heq_of_eq nativeHighStrongH3_normedSpace_eq_stage⟩

lemma normedSourceCLMNorm_nativeHighStrong_transport
    (T : normedSourceCLMCarrier (BallSobolev 3) (SphereSobolev (3/2 : ℝ))
      nativeStageH3NormedSourceData) :
    @norm (normedSourceCLMCarrier (BallSobolev 3) (SphereSobolev (3/2 : ℝ))
        nativeHighStrongH3NormedSourceData)
      (normedSourceCLMNorm (BallSobolev 3) (SphereSobolev (3/2 : ℝ))
        nativeHighStrongH3NormedSourceData)
      (Eq.mp (congrArg
        (normedSourceCLMCarrier (BallSobolev 3) (SphereSobolev (3/2 : ℝ)))
        nativeHighStrongH3NormedSourceData_eq_stage.symm) T) =
    @norm (normedSourceCLMCarrier (BallSobolev 3) (SphereSobolev (3/2 : ℝ))
        nativeStageH3NormedSourceData)
      (normedSourceCLMNorm (BallSobolev 3) (SphereSobolev (3/2 : ℝ))
        nativeStageH3NormedSourceData) T := by
  exact normedSourceCLMNorm_eq_of_data_eq
    (BallSobolev 3) (SphereSobolev (3/2 : ℝ))
    nativeStageH3NormedSourceData nativeHighStrongH3NormedSourceData
    nativeHighStrongH3NormedSourceData_eq_stage.symm T

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongH3NormedSourceData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeStageH3NormedSourceData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongH3NormedSourceData_eq_stage
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normedSourceCLMNorm_nativeHighStrong_transport
