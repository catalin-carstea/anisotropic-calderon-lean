import Calderon.NativeH3ThreeHalfRotationTrace
import Calderon.SphereSobolevOrderOneRotation
import Calderon.NativeSmoothBallSobolevFamily

/-! Literal same rotation on native H3 data. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH2ThreeHalfValueTrace

attribute [local irreducible] nativeThreeHalfValueTraceL nativeH3ThreeHalfRotationTraceL
  sphereSobolevRotationL smoothBallSobolev

lemma nativeH3ThreeHalfRotationTraceL_endpoint_graph
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (U : BallSobolev 3) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U) =
      sphereSobolevRotationL (3/2 : ℝ) i j
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U)) := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  let W := nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U)
  have hRot : sphereSobolevCoefficientL (1/2 : ℝ) k (sphereSobolevRotationL (3/2 : ℝ) i j W) =
      SmoothSphereRotationProjection.harmonicSphereRotation k i j
        (sphereSobolevCoefficientL (3/2 : ℝ) k W) := by
    have hs : (3/2 : ℝ)-1 = 1/2 := by norm_num
    simpa only [sphereSobolevCoefficientL,hs] using
      (sphereSobolevCoefficientL_rotation (3/2 : ℝ) i j k W)
  have hCoeff : sphereSobolevCoefficientL (3/2 : ℝ) k W =
      SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k
        (τ0.valueTraceL (TauCeti.Wkp.firstOrder 2 U)) := by
    simpa only [TauCeti.Wkp.firstOrder_succ] using
      (sphereSobolevCoefficientL_nativeThreeHalfValueTraceL hcalc hF hO hD τ0
        (TauCeti.Wkp.lowerOrder 2 U) k)
  exact (sphereSobolevCoefficientL_inclusion (3/2 : ℝ) (1/2 : ℝ) (by norm_num) _ k).trans
    ((sphereSobolevCoefficientL_nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U k).trans
      ((congrArg (SmoothSphereRotationProjection.harmonicSphereRotation k i j) hCoeff.symm).trans hRot.symm))

lemma nativeH3ThreeHalfRotationTraceL_smooth_endpoint_graph
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (v : SmoothData) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j (smoothBallSobolev 3 v)) =
      sphereSobolevRotationL (3/2 : ℝ) i j
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 v)) :=
  (nativeH3ThreeHalfRotationTraceL_endpoint_graph hcalc hF hO hD τ0 i j (smoothBallSobolev 3 v)).trans
    (congrArg (fun U : BallSobolev 2 => sphereSobolevRotationL (3/2 : ℝ) i j
      (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 U)) (lowerOrder_smoothBallSobolev 2 v))

lemma contDiff_nativeH3ThreeHalfRotationTraceL_of_joint
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (F : P × R3 → ℝ) (hFjoint : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p => nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j
      (smoothBallSobolev 3 ⟨fun x => F (p,x),SpatialJetFields.contDiff_spatial_slice F hFjoint p⟩)) :=
  (nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j).contDiff.comp
    (contDiff_smoothBallSobolev_of_joint hcalc 3 F hFjoint)

end OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace

#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.nativeH3ThreeHalfRotationTraceL_endpoint_graph
#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.nativeH3ThreeHalfRotationTraceL_smooth_endpoint_graph
#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.contDiff_nativeH3ThreeHalfRotationTraceL_of_joint
