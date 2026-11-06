import Mathlib.Tactic.ApplyWith
import Calderon.SubmoduleRealNaturalStructureData
import Calderon.RealHarmonicInheritedStructureData
import Calderon.RealNormedGroupProjectionData
import Calderon.NativeStrongDirichletInverseForcingComposition
import Calderon.NativeSobolevStageStructure
import Calderon.SequenceLpInheritedStructureData
import Calderon.SequenceLpNaturalStructureData
import Calderon.InheritedNormedStructureData
import Calderon.LpInheritedStructureData
import Calderon.NativeHighSmoothMultiplierForcing
import Calderon.ActualReferenceInverseOneLowerCoherence
import Calderon.ActualReferenceSmoothMultiplierStrongDefect
import Calderon.ActualReferenceInvertibleStrongWeakCoherence

/-! Original stored H3 norm structures and same-function continuity transport; no new
analytic premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] harmonicSphereSubspace

def nativeHighStrongInputTopology : TopologicalSpace (SphereSobolev (3/2 : ℝ)) := by
  infer_instance

def nativeHighStrongOutputTopology : TopologicalSpace (BallSobolev 3) := by
  infer_instance

def highStrongNativeH3Group : NormedAddCommGroup (BallSobolev 3) :=
  TauCeti.SobolevStage.instNormedAddCommGroup (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 2

attribute [local instance] highStrongNativeH3Group

def highStrongNativeH3Space : NormedSpace ℝ (BallSobolev 3) :=
  TauCeti.SobolevStage.instNormedSpace (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 2

attribute [local instance] highStrongNativeH3Space

lemma nativeHighStrongOutputTopology_eq_highStrongNativeH3Group :
    nativeHighStrongOutputTopology =
      highStrongNativeH3Group.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  have hGroup := nativeSobolevSucc_normedAddCommGroup_eq_stage 2
  have hTopology := congrArg
    (fun G : NormedAddCommGroup (BallSobolev 3) =>
      G.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    hGroup
  dsimp (config := { instances := true }) only
    [nativeHighStrongOutputTopology, highStrongNativeH3Group, inferInstance]
  all_goals rfl

lemma continuous_highStrongNativeH3_of_continuous_native
    (f : SphereSobolev (3/2 : ℝ) → BallSobolev 3)
    (hf : @Continuous (SphereSobolev (3/2 : ℝ)) (BallSobolev 3)
      nativeHighStrongInputTopology nativeHighStrongOutputTopology f) :
    @Continuous (SphereSobolev (3/2 : ℝ)) (BallSobolev 3)
      nativeHighStrongInputTopology
      highStrongNativeH3Group.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace f := by
  exact (congrArg
    (fun T : TopologicalSpace (BallSobolev 3) =>
      @Continuous (SphereSobolev (3/2 : ℝ)) (BallSobolev 3)
        nativeHighStrongInputTopology T f)
    nativeHighStrongOutputTopology_eq_highStrongNativeH3Group).mp hf

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongInputTopology
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongOutputTopology
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.highStrongNativeH3Group
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.highStrongNativeH3Space
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongOutputTopology_eq_highStrongNativeH3Group
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_highStrongNativeH3_of_continuous_native
