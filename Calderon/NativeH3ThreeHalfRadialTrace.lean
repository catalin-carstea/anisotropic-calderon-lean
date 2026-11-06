import Calderon.NativeSobolevCoordinateDerivativeCoherence
import Calderon.NativeThreeHalfCoefficientMultiplier
import Calderon.NativeFullHalfRadialTrace

/-! SAME native derivatives and radial lower graph. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeH3ThreeHalfRadialTrace
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH2ThreeHalfValueTrace NativeFullSharpHalfTrace NativeFullHalfRadialTrace

def nativeThreeHalfOutwardTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) : BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  ∑ i : Fin 3, (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
    (EuclideanSpace.single i 1)).comp
      ((nativeThreeHalfValueTraceL hcalc hF hO hD τ0).comp (unitBallCoordinateDerivativeL hcalc 2 i))

lemma nativeThreeHalfOutwardTraceL_apply (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 3) :
    nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 U =
      ∑ i : Fin 3, sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
        (EuclideanSpace.single i 1)
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (unitBallCoordinateDerivativeL hcalc 2 i U)) := by
  simp only [nativeThreeHalfOutwardTraceL,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]

attribute [local irreducible] nativeThreeHalfValueTraceL nativeHalfTraceL
  unitBallCoordinateDerivativeL sphereSobolevInclusionL sphereSobolevLinearCoordinateMulL

lemma sphereSobolevInclusionL_nativeThreeHalfOutwardTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 3) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 U) =
      nativeHalfOutwardTraceL hF hO hD hcalc τ0 (TauCeti.Wkp.lowerOrder 2 U) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let T := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let t := nativeHalfTraceL hF hO hD τ0
  let d (i : Fin 3) := unitBallCoordinateDerivativeL hcalc 2 i U
  let D (i : Fin 3) := unitBallCoordinateDerivativeL hcalc 1 i (TauCeti.Wkp.lowerOrder 2 U)
  let M (i : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)
  let m (i : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)
  have hTrace (i : Fin 3) : I (T (d i)) = t (TauCeti.Wkp.firstOrder 0 (D i)) := by
    have hHigh := sphereSobolevInclusionL_nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (d i)
    exact hHigh.trans (congrArg t (firstOrder_unitBallCoordinateDerivativeL_H3 hcalc i U))
  have hTerm (i : Fin 3) : I (M i (T (d i))) = m i (t (TauCeti.Wkp.firstOrder 0 (D i))) :=
    (sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (EuclideanSpace.single i 1) (T (d i))).trans (congrArg (m i) (hTrace i))
  have hPoint := congrArg I (nativeThreeHalfOutwardTraceL_apply hcalc hF hO hD τ0 U)
  have hSum : I (∑ i : Fin 3, M i (T (d i))) =
      ∑ i : Fin 3, m i (t (TauCeti.Wkp.firstOrder 0 (D i))) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => hTerm i)
  exact hPoint.trans (hSum.trans
    (nativeHalfOutwardTraceL_apply hF hO hD hcalc τ0 (TauCeti.Wkp.lowerOrder 2 U)).symm)

end OAI.AnisotropicCalderon.NativeH3ThreeHalfRadialTrace

#print axioms OAI.AnisotropicCalderon.NativeH3ThreeHalfRadialTrace.nativeThreeHalfOutwardTraceL
#print axioms OAI.AnisotropicCalderon.NativeH3ThreeHalfRadialTrace.nativeThreeHalfOutwardTraceL_apply
#print axioms OAI.AnisotropicCalderon.NativeH3ThreeHalfRadialTrace.sphereSobolevInclusionL_nativeThreeHalfOutwardTraceL

