import Calderon.NativeFullSharpHalfTrace
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.NativeCoordinateTraceVariation

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Classical
namespace OAI.AnisotropicCalderon.NativeFullHalfRadialTrace
open NativeFullSharpHalfTrace SphereHarmonic SpectralCoreRegularity DirichletFamily EnergyBridge

/-! Expanded before source in EXPANSION-native-full-H2-half-radial-trace-v001.json.
This uses the actual full native H1 sharp trace, whose genuine density parent must pass. -/

def nativeHalfOutwardTraceL (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) :
    BallSobolev 2 →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ i : Fin 3, (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
    (EuclideanSpace.single i 1)).comp
      ((nativeHalfTraceL hF hO hD τ0).comp
        ((TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3))
          (Omega := ballOpens) (p := 2) 0).comp (unitBallCoordinateDerivativeL hcalc 1 i)))

lemma nativeHalfOutwardTraceL_apply
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (u : BallSobolev 2) :
    nativeHalfOutwardTraceL hF hO hD hcalc τ0 u =
      ∑ i : Fin 3, sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1) (nativeHalfTraceL hF hO hD τ0
          (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u))) := by
  simp only [nativeHalfOutwardTraceL,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun v : BallH1 => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
    (EuclideanSpace.single i 1) (nativeHalfTraceL hF hO hD τ0 v))
      (TauCeti.Wkp.firstOrderL_apply (mu := (volume : Measure R3))
        (Omega := ballOpens) (p := 2) 0 (unitBallCoordinateDerivativeL hcalc 1 i u))

lemma sphereSobolevInclusionL_nativeHalfOutwardTraceL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (u : BallSobolev 2) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (nativeHalfOutwardTraceL hF hO hD hcalc τ0 u) =
        sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 u) := by
  rw [nativeHalfOutwardTraceL_apply,map_sum,outwardRadialTraceL_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD (1/2 : ℝ)
    (by norm_num) (EuclideanSpace.single i 1)
      (nativeHalfTraceL hF hO hD τ0
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u)))
      (τ0.valueTraceL (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u)))
      (sphereSobolevInclusionL_nativeHalfTraceL hF hO hD τ0
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u)))
  simpa only [sphereLinearCoordinateMulL_single] using h

lemma sphereSobolevCoefficientL_nativeHalfOutwardTraceL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (u : BallSobolev 2) (k : ℕ) :
    sphereSobolevCoefficientL (1/2 : ℝ) k (nativeHalfOutwardTraceL hF hO hD hcalc τ0 u) =
      sphereHarmonicCoordinate hO hD k (outwardRadialTraceL hcalc τ0 u) := by
  have h := congrArg (sphereSobolevCoefficientL 0 k)
    (sphereSobolevInclusionL_nativeHalfOutwardTraceL hF hO hD hcalc τ0 u)
  simpa only [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv] using h

def nativeHalfOutwardTraceBound (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) : ℝ :=
  ∑ i : Fin 3, ‖sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
    (EuclideanSpace.single i 1)‖ * nativeHalfTraceBound τ0 * ‖unitBallCoordinateDerivativeL hcalc 1 i‖

lemma norm_nativeHalfOutwardTraceL_apply_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (u : BallSobolev 2) :
    ‖nativeHalfOutwardTraceL hF hO hD hcalc τ0 u‖ ≤
      nativeHalfOutwardTraceBound hF hO hD hcalc τ0*‖u‖ := by
  rw [nativeHalfOutwardTraceL_apply,nativeHalfOutwardTraceBound,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ ‖sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)‖ *
        ‖nativeHalfTraceL hF hO hD τ0
          (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u))‖ :=
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1)).le_opNorm _
    _ ≤ ‖sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)‖ *
        (nativeHalfTraceBound τ0 *
          ‖TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u)‖) :=
      mul_le_mul_of_nonneg_left (norm_nativeHalfTrace_le hF hO hD τ0 _) (norm_nonneg (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1)))
    _ ≤ ‖sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)‖ *
        (nativeHalfTraceBound τ0 * ‖unitBallCoordinateDerivativeL hcalc 1 i u‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (norm_unitBall_firstOrder_le 0 _) (Real.sqrt_nonneg _)) (norm_nonneg (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1)))
    _ ≤ ‖sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)‖ *
        (nativeHalfTraceBound τ0 * (‖unitBallCoordinateDerivativeL hcalc 1 i‖*‖u‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        ((unitBallCoordinateDerivativeL hcalc 1 i).le_opNorm u) (Real.sqrt_nonneg _))
          (norm_nonneg (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
            (EuclideanSpace.single i 1)))
    _ = _ := by ring

lemma norm_nativeHalfOutwardTraceL_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) :
    ‖nativeHalfOutwardTraceL hF hO hD hcalc τ0‖ ≤
      nativeHalfOutwardTraceBound hF hO hD hcalc τ0 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · unfold nativeHalfOutwardTraceBound
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg
      (norm_nonneg (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1))) (Real.sqrt_nonneg _))
      (norm_nonneg (unitBallCoordinateDerivativeL hcalc 1 i))
  · intro u
    exact norm_nativeHalfOutwardTraceL_apply_le hF hO hD hcalc τ0 u

end OAI.AnisotropicCalderon.NativeFullHalfRadialTrace

#print axioms OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.nativeHalfOutwardTraceL
#print axioms OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.nativeHalfOutwardTraceL_apply
#print axioms OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.sphereSobolevInclusionL_nativeHalfOutwardTraceL
#print axioms OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.sphereSobolevCoefficientL_nativeHalfOutwardTraceL
#print axioms OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.nativeHalfOutwardTraceBound
#print axioms OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.norm_nativeHalfOutwardTraceL_apply_le
#print axioms OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.norm_nativeHalfOutwardTraceL_le
