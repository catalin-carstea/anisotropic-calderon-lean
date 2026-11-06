import Mathlib.Data.Sigma.Basic
import Calderon.NativeH3ThreeHalfRadialTrace
import Calderon.NativeHighStrongSobolevTopology
import Calderon.NativeHighStrongH3StructureEquality
import Calderon.InnerProductMeasureSpaceProjectionData
import Calderon.NativeOutwardActualCarrierEquality
import Calderon.NativeHighStrongOutwardPublicCarrierEquality

/-! Full before-source: weak-native-instance-repair-author-oct16-v001/
EXPANSION-native-outward-post-context-and-full-carrier-v113.md. Exact pre/post native public carrier coherence and full actual-to-selected-native Type equality; no new norm or trace premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH3ThreeHalfRadialTrace

attribute [local instance_reducible] highStrongNativeH3Group
attribute [local instance_reducible] highStrongNativeH3Space
attribute [local instance] highStrongNativeH3Group
attribute [local instance] highStrongNativeH3Space

attribute [local irreducible] TauCeti.SobolevStage.instNormedAddCommGroup
attribute [local irreducible] TauCeti.SobolevStage.instNormedSpace

lemma nativeHighStrongOutwardPublicCarrier_eq_native_context
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    nativeHighStrongOutwardPublicCarrier =
      (BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ)) := by
  rfl

lemma nativeOutwardActualCarrier_eq_native
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    nativeOutwardActualCarrier hcalc hF hO hD τ0 =
      (BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ)) := by
  let SourceData : Type :=
    Σ G : NormedAddCommGroup (BallSobolev 3),
      @NormedSpace ℝ (BallSobolev 3) Real.normedField
        (@NormedAddCommGroup.toSeminormedAddCommGroup (BallSobolev 3) G)
  let chosen : SourceData := ⟨highStrongNativeH3Group, highStrongNativeH3Space⟩
  let original : SourceData :=
    ⟨TauCeti.SobolevStage.instNormedAddCommGroup
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2,
      TauCeti.SobolevStage.instNormedSpace
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2⟩
  have hSpace : HEq chosen.2 original.2 :=
    heq_of_eq nativeHighStrongH3_normedSpace_eq_stage
  have hData : chosen = original :=
    Sigma.mk.inj_iff.mpr
      ⟨nativeHighStrongH3_normedAddCommGroup_eq_stage, hSpace⟩
  let Carrier (d : SourceData) : Type :=
    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      (BallSobolev 3)
      d.1.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      d.1.toAddCommGroup.toAddCommMonoid
      (SphereSobolev (3/2 : ℝ))
      (inferInstance : TopologicalSpace (SphereSobolev (3/2 : ℝ)))
      (inferInstance : AddCommMonoid (SphereSobolev (3/2 : ℝ)))
      (@NormedSpace.toModule ℝ (BallSobolev 3) Real.normedField
        (@NormedAddCommGroup.toSeminormedAddCommGroup (BallSobolev 3) d.1) d.2)
      (inferInstance : Module ℝ (SphereSobolev (3/2 : ℝ)))
  have hCarrier := congrArg Carrier hData
  have hActualStage := nativeOutwardActualCarrier_eq_stage hcalc hF hO hD τ0
  have hChosenPublic : Carrier chosen = nativeHighStrongOutwardPublicCarrier :=
    nativeHighStrongOutwardChosenCarrier_eq_public
  have hPublicNative :=
    nativeHighStrongOutwardPublicCarrier_eq_native_context hcalc hF hO hD τ0
  exact hActualStage.trans (hCarrier.symm.trans (hChosenPublic.trans hPublicNative))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongOutwardPublicCarrier_eq_native_context
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeOutwardActualCarrier_eq_native
