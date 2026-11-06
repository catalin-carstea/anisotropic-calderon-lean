import Calderon.NativeH3FiveHalfValueTrace
import Calderon.NativeH3CoefficientConormalTrace
import Calderon.NativeCoefficientMultiplierOrderCoherence

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeH4FiveHalfCoefficientConormalTrace
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH3FiveHalfValueTrace NativeH3CoefficientConormalTrace NativeH2ThreeHalfValueTrace

/-- The order-four coefficient conormal trace with five-half angular regularity. -/
def nativeFiveHalfCoefficientConormalTraceL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 4) :
    BallSobolev 4 →L[ℝ] SphereSobolev (5/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (sphereSobolevLinearCoordinateMulL hF hO hD (5/2 : ℝ)
      (EuclideanSpace.single i 1)).comp
      ((nativeFiveHalfValueTraceL hcalc hF hO hD τ0).comp
        ((coefficientMultiplier hcalc 3 (F i j)).comp
          (unitBallCoordinateDerivativeL hcalc 3 j)))

theorem nativeFiveHalfCoefficientConormalTraceL_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 4) (U : BallSobolev 4) :
    nativeFiveHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F U =
      ∑ i : Fin 3, ∑ j : Fin 3,
        sphereSobolevLinearCoordinateMulL hF hO hD (5/2 : ℝ)
          (EuclideanSpace.single i 1)
          (nativeFiveHalfValueTraceL hcalc hF hO hD τ0
            (coefficientMultiplier hcalc 3 (F i j) (unitBallCoordinateDerivativeL hcalc 3 j U))) := by
  simp only [nativeFiveHalfCoefficientConormalTraceL,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]

attribute [local irreducible] nativeFiveHalfValueTraceL nativeThreeHalfValueTraceL
  unitBallCoordinateDerivativeL sphereSobolevInclusionL sphereSobolevLinearCoordinateMulL
  coefficientMultiplier

/-- Exact inclusion identifies the order-four trace with the same order-three
conormal trace on the lowered input and lowered coefficient jets. -/
theorem sphereSobolevInclusionL_nativeFiveHalfCoefficientConormalTraceL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 4) (G : SmoothCoefficientMatrix 3)
    (hFG : ∀ i j, coefficientValue 4 (F i j) = coefficientValue 3 (G i j))
    (U : BallSobolev 4) :
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (nativeFiveHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F U) =
    nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 G
      (TauCeti.Wkp.lowerOrder 3 U) := by
  let I := sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
  let T := nativeFiveHalfValueTraceL hcalc hF hO hD τ0
  let t := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let d (i j : Fin 3) := coefficientMultiplier hcalc 3 (F i j)
    (unitBallCoordinateDerivativeL hcalc 3 j U)
  let D (i j : Fin 3) := coefficientMultiplier hcalc 2 (G i j)
    (unitBallCoordinateDerivativeL hcalc 2 j (TauCeti.Wkp.lowerOrder 3 U))
  let M (i : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (5/2 : ℝ)
    (EuclideanSpace.single i 1)
  let m (i : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
    (EuclideanSpace.single i 1)
  have hLower (i j : Fin 3) : TauCeti.Wkp.lowerOrder 2 (d i j) = D i j := by
    exact (lowerOrder_coefficientMultiplier_of_value_eq hcalc 2 (F i j) (G i j)
      (hFG i j) (unitBallCoordinateDerivativeL hcalc 3 j U)).trans
        (congrArg (coefficientMultiplier hcalc 2 (G i j))
          (lowerOrder_unitBallCoordinateDerivativeL hcalc 2 j U))
  have hTrace (i j : Fin 3) : I (T (d i j)) = t (D i j) := by
    have hHigh := sphereSobolevInclusionL_nativeFiveHalfValueTraceL hcalc hF hO hD τ0 (d i j)
    exact hHigh.trans (congrArg t (hLower i j))
  have hTerm (i j : Fin 3) : I (M i (T (d i j))) = m i (t (D i j)) :=
    (sphereSobolevInclusionL_linearCoordinateMul hF hO hD (5/2 : ℝ) (3/2 : ℝ)
      (by norm_num) (EuclideanSpace.single i 1) (T (d i j))).trans
        (congrArg (m i) (hTrace i j))
  rw [nativeFiveHalfCoefficientConormalTraceL_apply,map_sum]
  simp_rw [map_sum]
  rw [nativeThreeHalfCoefficientConormalTraceL_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hTerm i j

end OAI.AnisotropicCalderon.NativeH4FiveHalfCoefficientConormalTrace
