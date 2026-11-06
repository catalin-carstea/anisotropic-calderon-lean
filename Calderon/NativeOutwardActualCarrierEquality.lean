import Mathlib.Data.Sigma.Basic
import Calderon.NativeH3ThreeHalfRadialTrace
import Calderon.NativeHighStrongSobolevTopology
import Calderon.NativeHighStrongH3StructureEquality
import Calderon.InnerProductMeasureSpaceProjectionData

/-! Before-source: weak-native-instance-repair-author-oct16-v001/
EXPANSION-native-outward-actual-carrier-capture-v104.md.
The exact inferred native carrier and its mandatory original Stage carrier equality. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH3ThreeHalfRadialTrace
attribute [local instance_reducible] highStrongNativeH3Group
attribute [local instance_reducible] highStrongNativeH3Space
attribute [local instance] highStrongNativeH3Group
attribute [local instance] highStrongNativeH3Space

def nativeOutwardActualCarrier
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    Type :=
  (fun {A : Type} (_ : A) => A)
    (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0)

attribute [local irreducible] TauCeti.SobolevStage.instNormedAddCommGroup
attribute [local irreducible] TauCeti.SobolevStage.instNormedSpace
lemma nativeOutwardActualCarrier_eq_stage
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    nativeOutwardActualCarrier hcalc hF hO hD τ0 =
    (@ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      (BallSobolev 3)
      (TauCeti.SobolevStage.instNormedAddCommGroup
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (TauCeti.SobolevStage.instNormedAddCommGroup
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2).toAddCommGroup.toAddCommMonoid
      (SphereSobolev (3/2 : ℝ))
      (inferInstance : TopologicalSpace (SphereSobolev (3/2 : ℝ)))
      (inferInstance : AddCommMonoid (SphereSobolev (3/2 : ℝ)))
      (@NormedSpace.toModule ℝ (BallSobolev 3) Real.normedField
        (@NormedAddCommGroup.toSeminormedAddCommGroup (BallSobolev 3)
          (TauCeti.SobolevStage.instNormedAddCommGroup
            (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
            (Omega := ballOpens) (p := 2) 2))
        (TauCeti.SobolevStage.instNormedSpace
          (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
          (Omega := ballOpens) (p := 2) 2))
      (inferInstance : Module ℝ (SphereSobolev (3/2 : ℝ)))) := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeOutwardActualCarrier
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeOutwardActualCarrier_eq_stage
