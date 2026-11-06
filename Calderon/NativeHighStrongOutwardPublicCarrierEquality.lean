import Mathlib.Data.Sigma.Basic
import Calderon.NativeH3ThreeHalfRadialTrace
import Calderon.NativeHighStrongSobolevTopology
import Calderon.NativeHighStrongH3StructureEquality
import Calderon.InnerProductMeasureSpaceProjectionData
import Calderon.NativeOutwardActualCarrierEquality

/-! Exact original native public carrier versus its stored full-data CLM13 expansion. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH3ThreeHalfRadialTrace

attribute [local instance_reducible] highStrongNativeH3Group
attribute [local instance_reducible] highStrongNativeH3Space
attribute [local instance] highStrongNativeH3Group
attribute [local instance] highStrongNativeH3Space

def nativeHighStrongOutwardPublicCarrier : Type :=
  BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ)

attribute [local irreducible] TauCeti.SobolevStage.instNormedAddCommGroup
attribute [local irreducible] TauCeti.SobolevStage.instNormedSpace

lemma nativeHighStrongOutwardChosenCarrier_eq_public :
    (@ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      (BallSobolev 3)
      highStrongNativeH3Group.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      highStrongNativeH3Group.toAddCommGroup.toAddCommMonoid
      (SphereSobolev (3/2 : ℝ))
      (inferInstance : TopologicalSpace (SphereSobolev (3/2 : ℝ)))
      (inferInstance : AddCommMonoid (SphereSobolev (3/2 : ℝ)))
      (@NormedSpace.toModule ℝ (BallSobolev 3) Real.normedField
        (@NormedAddCommGroup.toSeminormedAddCommGroup (BallSobolev 3) highStrongNativeH3Group)
        highStrongNativeH3Space)
      (inferInstance : Module ℝ (SphereSobolev (3/2 : ℝ)))) =
      nativeHighStrongOutwardPublicCarrier := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongOutwardPublicCarrier
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongOutwardChosenCarrier_eq_public
