import Calderon.NativeLowerOrderProjection
import Calderon.NativeH3ThreeHalfRotationTrace
import Calderon.SphereSobolevFiveHalfTraceReconstruction

/-! Native H3 value trace with exact lower coherence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  SpectralCoreRegularity NativeH2ThreeHalfValueTrace

attribute [local irreducible] nativeLowerOrderL nativeThreeHalfValueTraceL nativeH3ThreeHalfRotationTraceL
  sphereSobolevFiveHalfTraceReconstructionIdentityL sphereSobolevFiveHalfTraceReconstructionRotationL


def nativeFiveHalfValueTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) : BallSobolev 3 →L[ℝ] SphereSobolev (5/2 : ℝ) :=
  let T : BallSobolev 2 →L[ℝ] SphereSobolev (3/2 : ℝ) :=
    nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let L2 : BallSobolev 3 →L[ℝ] BallSobolev 2 :=
    nativeLowerOrderL 2
  let A : BallSobolev 3 →L[ℝ] SphereSobolev (5/2 : ℝ) :=
    sphereSobolevFiveHalfTraceReconstructionIdentityL.comp (T.comp L2)
  let R : Fin 3 → Fin 3 → BallSobolev 3 →L[ℝ] SphereSobolev (5/2 : ℝ) := fun i j =>
    (sphereSobolevFiveHalfTraceReconstructionRotationL i j).comp
      (nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j)
  A + ∑ i : Fin 3, ∑ j : Fin 3, R i j


lemma sphereSobolevCoefficientL_nativeFiveHalfValueTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 3) (k : ℕ) :
    sphereSobolevCoefficientL (5/2 : ℝ) k (nativeFiveHalfValueTraceL hcalc hF hO hD τ0 U) =
      sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (TauCeti.Wkp.firstOrder 2 U)) := by
  have hPoint : nativeFiveHalfValueTraceL hcalc hF hO hD τ0 U =
      sphereSobolevFiveHalfTraceReconstructionIdentityL
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U)) +
      ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevFiveHalfTraceReconstructionRotationL i j
        (nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U) := by
    simp only [nativeFiveHalfValueTraceL,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
    exact congrArg (fun V : BallSobolev 2 =>
      sphereSobolevFiveHalfTraceReconstructionIdentityL
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 V) +
        ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevFiveHalfTraceReconstructionRotationL i j
          (nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U))
      (nativeLowerOrderL_apply 2 U)
  have hRecon := sphereSobolevCoefficientL_fiveHalfTraceReconstruction
    (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U))
    (fun i j => nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U)
    (fun i j k => nativeH3ThreeHalfRotationTraceL_storedGraph hcalc hF hO hD τ0 i j U k) k
  have hFirst : TauCeti.Wkp.firstOrder 2 U =
      TauCeti.Wkp.firstOrder 1 (TauCeti.Wkp.lowerOrder 2 U) :=
    TauCeti.Wkp.firstOrder_succ 1 U
  exact ((congrArg (sphereSobolevCoefficientL (5/2 : ℝ) k) hPoint).trans
    (hRecon.trans (sphereSobolevCoefficientL_nativeThreeHalfValueTraceL
      hcalc hF hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U) k))).trans
        (congrArg (fun V : BallH1 => sphereHarmonicCoordinate hO hD k (τ0.valueTraceL V))
          hFirst.symm)

lemma sphereSobolevInclusionL_nativeFiveHalfValueTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 3) :
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (nativeFiveHalfValueTraceL hcalc hF hO hD τ0 U) =
      nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U) := by
  apply sphereSobolev_ext (3/2 : ℝ)
  intro k
  have hFirst : TauCeti.Wkp.firstOrder 2 U =
      TauCeti.Wkp.firstOrder 1 (TauCeti.Wkp.lowerOrder 2 U) :=
    TauCeti.Wkp.firstOrder_succ 1 U
  calc
    _ = sphereSobolevCoefficientL (5/2 : ℝ) k
        (nativeFiveHalfValueTraceL hcalc hF hO hD τ0 U) :=
      sphereSobolevCoefficientL_inclusion _ _ _ _ _
    _ = sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (TauCeti.Wkp.firstOrder 2 U)) :=
      sphereSobolevCoefficientL_nativeFiveHalfValueTraceL hcalc hF hO hD τ0 U k
    _ = sphereHarmonicCoordinate hO hD k
        (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 (TauCeti.Wkp.lowerOrder 2 U))) :=
      congrArg (fun V : BallH1 => sphereHarmonicCoordinate hO hD k (τ0.valueTraceL V)) hFirst
    _ = _ := (sphereSobolevCoefficientL_nativeThreeHalfValueTraceL
      hcalc hF hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U) k).symm

lemma sphereSobolevInclusionL_nativeFiveHalfValueTraceL_smoothBallSobolev
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (f : SmoothData) :
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (nativeFiveHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 3 f)) =
      nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 f) := by
  exact (sphereSobolevInclusionL_nativeFiveHalfValueTraceL hcalc hF hO hD τ0
    (smoothBallSobolev 3 f)).trans
      (congrArg (nativeThreeHalfValueTraceL hcalc hF hO hD τ0) (lowerOrder_smoothBallSobolev 2 f))

end OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace

#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.nativeFiveHalfValueTraceL
#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.sphereSobolevCoefficientL_nativeFiveHalfValueTraceL
#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.sphereSobolevInclusionL_nativeFiveHalfValueTraceL
#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.sphereSobolevInclusionL_nativeFiveHalfValueTraceL_smoothBallSobolev

