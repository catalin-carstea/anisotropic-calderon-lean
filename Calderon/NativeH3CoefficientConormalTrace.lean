import Calderon.NativeH3ThreeHalfRadialTrace
import Calderon.NativeHalfCoefficientConormalTrace
import Calderon.NativeCoefficientMultiplierOrderCoherence

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeH3CoefficientConormalTrace
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH2ThreeHalfValueTrace NativeFullSharpHalfTrace NativeHalfCoefficientConormalTrace

def nativeThreeHalfCoefficientConormalTraceL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 3) :
    BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
      (EuclideanSpace.single i 1)).comp
      ((nativeThreeHalfValueTraceL hcalc hF hO hD τ0).comp
        ((coefficientMultiplier hcalc 2 (F i j)).comp
          (unitBallCoordinateDerivativeL hcalc 2 j)))

theorem nativeThreeHalfCoefficientConormalTraceL_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 3) (U : BallSobolev 3) :
    nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F U =
      ∑ i : Fin 3, ∑ j : Fin 3,
        sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
          (EuclideanSpace.single i 1)
          (nativeThreeHalfValueTraceL hcalc hF hO hD τ0
            (coefficientMultiplier hcalc 2 (F i j) (unitBallCoordinateDerivativeL hcalc 2 j U))) := by
  simp only [nativeThreeHalfCoefficientConormalTraceL,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]

attribute [local irreducible] nativeThreeHalfValueTraceL nativeHalfTraceL
  unitBallCoordinateDerivativeL sphereSobolevInclusionL sphereSobolevLinearCoordinateMulL
  coefficientMultiplier

theorem sphereSobolevInclusionL_nativeThreeHalfCoefficientConormalTraceL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 3) (G : SmoothCoefficientMatrix 2)
    (hFG : ∀ i j, coefficientValue 3 (F i j) = coefficientValue 2 (G i j))
    (U : BallSobolev 3) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F U) =
    nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 G (TauCeti.Wkp.lowerOrder 2 U) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let T := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let t := nativeHalfTraceL hF hO hD τ0
  let d (i j : Fin 3) := coefficientMultiplier hcalc 2 (F i j)
    (unitBallCoordinateDerivativeL hcalc 2 j U)
  let D (i j : Fin 3) := coefficientMultiplier hcalc 1 (G i j)
    (unitBallCoordinateDerivativeL hcalc 1 j (TauCeti.Wkp.lowerOrder 2 U))
  let M (i : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
    (EuclideanSpace.single i 1)
  let m (i : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
    (EuclideanSpace.single i 1)
  have hLower (i j : Fin 3) : TauCeti.Wkp.lowerOrder 1 (d i j) = D i j := by
    exact (lowerOrder_coefficientMultiplier_of_value_eq hcalc 1 (F i j) (G i j)
      (hFG i j) (unitBallCoordinateDerivativeL hcalc 2 j U)).trans
        (congrArg (coefficientMultiplier hcalc 1 (G i j))
          (firstOrder_unitBallCoordinateDerivativeL_H3 hcalc j U))
  have hTrace (i j : Fin 3) : I (T (d i j)) = t (TauCeti.Wkp.firstOrder 0 (D i j)) := by
    have hHigh := sphereSobolevInclusionL_nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (d i j)
    exact hHigh.trans (congrArg t (hLower i j))
  have hTerm (i j : Fin 3) : I (M i (T (d i j))) =
      m i (t (TauCeti.Wkp.firstOrder 0 (D i j))) :=
    (sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (EuclideanSpace.single i 1) (T (d i j))).trans
        (congrArg (m i) (hTrace i j))
  rw [nativeThreeHalfCoefficientConormalTraceL_apply,map_sum]
  simp_rw [map_sum]
  rw [nativeHalfCoefficientConormalTraceL_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hTerm i j

theorem sphereSobolevInclusionL_zero_nativeThreeHalfCoefficientConormalTraceL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 3) (G : SmoothCoefficientMatrix 2)
    (hFG : ∀ i j, coefficientValue 3 (F i j) = coefficientValue 2 (G i j))
    (U : BallSobolev 3) :
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
      (nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F U) =
    sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 G (TauCeti.Wkp.lowerOrder 2 U)) := by
  have hTrans := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 =>
      A (nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F U))
    (sphereSobolevInclusionL_trans (3/2 : ℝ) (1/2 : ℝ) 0 (by norm_num) (by norm_num))
  exact hTrans.symm.trans ((congrArg
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num))
    (sphereSobolevInclusionL_nativeThreeHalfCoefficientConormalTraceL
      hcalc hF hO hD τ0 F G hFG U)).trans
        (sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL
          hF hO hD hcalc τ0 G (TauCeti.Wkp.lowerOrder 2 U)))


theorem contDiffOn_nativeThreeHalfCoefficientConormalTraceL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : E → SmoothCoefficientMatrix 3) (s : Set E)
    (hFcoeff : ∀ i j, ContDiffOn ℝ n (fun p => F p i j) s) :
    ContDiffOn ℝ n (fun p => nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 (F p)) s := by
  unfold nativeThreeHalfCoefficientConormalTraceL
  refine ContDiffOn.sum fun i _ => ?_
  refine ContDiffOn.sum fun j _ => ?_
  have hM : ContDiffOn ℝ n (fun p => coefficientMultiplier hcalc 2 (F p i j)) s := by
    have heq : (fun p => coefficientMultiplierL hcalc 2 (F p i j)) =
        (fun p => coefficientMultiplier hcalc 2 (F p i j)) :=
      funext fun p => coefficientMultiplierL_apply hcalc 2 (F p i j)
    rw [← heq]
    exact contDiffOn_coefficientMultiplier hcalc 2 (fun p => F p i j) s (hFcoeff i j)
  exact contDiffOn_const.clm_comp
    (contDiffOn_const.clm_comp (hM.clm_comp contDiffOn_const))

end OAI.AnisotropicCalderon.NativeH3CoefficientConormalTrace
