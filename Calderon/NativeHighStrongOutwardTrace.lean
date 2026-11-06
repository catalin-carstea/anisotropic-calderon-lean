import Mathlib.Data.Sigma.Basic
import Calderon.NativeH3ThreeHalfRadialTrace
import Calderon.NativeHighStrongSobolevTopology
import Calderon.NativeHighStrongH3StructureEquality
import Calderon.InnerProductMeasureSpaceProjectionData
import Calderon.NativeOutwardActualCarrierEquality
import Calderon.NativeHighStrongOutwardPublicCarrierEquality
import Calderon.NativeHighStrongOutwardNativeCarrierEquality

/-! Before-source: weak-native-instance-repair-author-oct16-v001/
EXPANSION-small-native-outward-trace-transport-v085.md. The same actual outward trace in the checked stored H3 context. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH3ThreeHalfRadialTrace

attribute [local instance_reducible] highStrongNativeH3Group
attribute [local instance_reducible] highStrongNativeH3Space
attribute [local instance] highStrongNativeH3Group
attribute [local instance] highStrongNativeH3Space

def nativeHighStrongH3_topology_eq_stage :=
  congrArg
    (fun G : NormedAddCommGroup (BallSobolev 3) =>
      (G.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :
        TopologicalSpace (BallSobolev 3)))
    nativeHighStrongH3_normedAddCommGroup_eq_stage

def nativeHighStrongH3_addCommMonoid_eq_stage :=
  congrArg
    (fun G : NormedAddCommGroup (BallSobolev 3) =>
      (G.toAddCommGroup.toAddCommMonoid : AddCommMonoid (BallSobolev 3)))
    nativeHighStrongH3_normedAddCommGroup_eq_stage

def nativeHighStrongH3_module_eq_stage :=
  congrArg
    (fun S : @NormedSpace ℝ (BallSobolev 3) Real.normedField
      (@NormedAddCommGroup.toSeminormedAddCommGroup (BallSobolev 3) highStrongNativeH3Group) =>
      @NormedSpace.toModule ℝ (BallSobolev 3) Real.normedField
        (@NormedAddCommGroup.toSeminormedAddCommGroup (BallSobolev 3) highStrongNativeH3Group) S)
    nativeHighStrongH3_normedSpace_eq_stage

attribute [local irreducible] TauCeti.SobolevStage.instNormedAddCommGroup
attribute [local irreducible] TauCeti.SobolevStage.instNormedSpace

def nativeHighStrongOutwardTraceL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ) := by
  dbg_trace "NATIVE_OUTWARD_FULL_CARRIER_FACTORY_ENTER"
  let actualNative : nativeOutwardActualCarrier hcalc hF hO hD τ0 :=
    nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0
  dbg_trace "NATIVE_OUTWARD_FULL_CARRIER_ACTUAL_TYPED"
  have hNativeCarrier := nativeOutwardActualCarrier_eq_native hcalc hF hO hD τ0
  dbg_trace "NATIVE_OUTWARD_FULL_CARRIER_EQUALITY_READY"
  let nativeValue := Eq.mp hNativeCarrier actualNative
  dbg_trace "NATIVE_OUTWARD_FULL_CARRIER_VALUE_TYPED"
  exact nativeValue

lemma nativeHighStrongOutwardTraceL_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (v : BallSobolev 3) :
    nativeHighStrongOutwardTraceL hcalc hF hO hD τ0 v =
      nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 v := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongH3_topology_eq_stage
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongH3_addCommMonoid_eq_stage
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongH3_module_eq_stage
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongOutwardTraceL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongOutwardTraceL_apply
