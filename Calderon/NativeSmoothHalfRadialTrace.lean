import Calderon.NativeSmoothSharpTraceCompletion
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.NativeCoordinateTraceVariation

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Classical
namespace OAI.AnisotropicCalderon.NativeSmoothHalfRadialTrace
open NativeSmoothSharpTraceCompletion NativePolynomialBulkMoments SphereHarmonic
  SpectralCoreRegularity DirichletFamily EnergyBridge

/-! The global smooth domain is explicit. -/

lemma sphereSobolevInclusionL_smoothHalfTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (f : SmoothData) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (smoothHalfTrace hF hO hD τ0 f) =
      sphereSobolevZeroEquiv hO hD (τ0.valueTraceL (smoothSobolev f)) := by
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_smoothHalfTrace,
    sphereSobolevCoefficientL_zeroEquiv]

def smoothHalfOutwardTrace (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (f : SmoothData) :
    SphereSobolev (1/2 : ℝ) :=
  ∑ i : Fin 3, sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
    (EuclideanSpace.single i 1)
      (smoothHalfTrace hF hO hD τ0 (smoothCoordinateDerivative f i))

attribute [local irreducible] smoothHalfTrace sphereSobolevLinearCoordinateMulL
  sphereSobolevInclusionL sphereSobolevZeroEquiv outwardRadialTraceL smoothBallSobolev

lemma sphereSobolevInclusionL_smoothHalfOutwardTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (f : SmoothData) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (smoothHalfOutwardTrace hF hO hD τ0 f) =
        sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 (smoothBallSobolev 2 f)) := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  have hTerm (i : Fin 3) :
      I (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1)
        (smoothHalfTrace hF hO hD τ0 (smoothCoordinateDerivative f i))) =
      Z (sphereCoordinateMulL i (τ0.valueTraceL
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i
          (smoothBallSobolev 2 f))))) := by
    have hDerivative : TauCeti.Wkp.firstOrder 0
        (unitBallCoordinateDerivativeL hcalc 1 i (smoothBallSobolev 2 f)) =
        smoothSobolev (smoothCoordinateDerivative f i) :=
      (congrArg (fun V : BallSobolev 1 => TauCeti.Wkp.firstOrder 0 V)
        (unitBallCoordinateDerivativeL_smoothBallSobolev hcalc 1 i f)).trans
          (firstOrder_smoothBallSobolev 0 (smoothCoordinateDerivative f i))
    have hMul := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD (1/2 : ℝ)
      (by norm_num) (EuclideanSpace.single i 1)
      (smoothHalfTrace hF hO hD τ0 (smoothCoordinateDerivative f i))
      (τ0.valueTraceL (smoothSobolev (smoothCoordinateDerivative f i)))
      (sphereSobolevInclusionL_smoothHalfTrace hF hO hD τ0 (smoothCoordinateDerivative f i))
    have hSingle : sphereLinearCoordinateMulL (EuclideanSpace.single i 1)
        (τ0.valueTraceL (smoothSobolev (smoothCoordinateDerivative f i))) =
        sphereCoordinateMulL i (τ0.valueTraceL (smoothSobolev (smoothCoordinateDerivative f i))) :=
      congrArg (fun T : SphereL2 →L[ℝ] SphereL2 =>
        T (τ0.valueTraceL (smoothSobolev (smoothCoordinateDerivative f i))))
        (sphereLinearCoordinateMulL_single i)
    exact hMul.trans ((congrArg Z hSingle).trans
      (congrArg (fun V : BallH1 => Z (sphereCoordinateMulL i (τ0.valueTraceL V)))
        hDerivative.symm))
  have hLeft : I (smoothHalfOutwardTrace hF hO hD τ0 f) =
      ∑ i : Fin 3, I (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1)
        (smoothHalfTrace hF hO hD τ0 (smoothCoordinateDerivative f i))) := by
    unfold smoothHalfOutwardTrace
    exact map_sum I _ _
  have hRight : Z (outwardRadialTraceL hcalc τ0 (smoothBallSobolev 2 f)) =
      ∑ i : Fin 3, Z (sphereCoordinateMulL i (τ0.valueTraceL
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i
          (smoothBallSobolev 2 f))))) :=
    (congrArg Z (outwardRadialTraceL_apply hcalc τ0 (smoothBallSobolev 2 f))).trans
      (map_sum Z _ _)
  exact hLeft.trans ((Finset.sum_congr rfl (fun i _ => hTerm i)).trans hRight.symm)

lemma norm_smoothCoordinateDerivative_smoothSobolev_le
    (hcalc : FixedSobolevCalculus) (f : SmoothData) (i : Fin 3) :
    ‖smoothSobolev (smoothCoordinateDerivative f i)‖ ≤
      ‖unitBallCoordinateDerivativeL hcalc 1 i‖*‖smoothBallSobolev 2 f‖ := by
  rw [← firstOrder_smoothBallSobolev 0,
    ← unitBallCoordinateDerivativeL_smoothBallSobolev hcalc 1 i f]
  exact (norm_unitBall_firstOrder_le 0 _).trans
    ((unitBallCoordinateDerivativeL hcalc 1 i).le_opNorm _)

lemma norm_smoothHalfOutwardTrace_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (f : SmoothData) :
    ‖smoothHalfOutwardTrace hF hO hD τ0 f‖ ≤
      ∑ i : Fin 3, ‖sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1)‖ * Real.sqrt (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass) *
          ‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖smoothBallSobolev 2 f‖ := by
  unfold smoothHalfOutwardTrace
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ ‖sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)‖ *
        ‖smoothHalfTrace hF hO hD τ0 (smoothCoordinateDerivative f i)‖ :=
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1)).le_opNorm _
    _ ≤ ‖sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)‖ *
        (Real.sqrt (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass) *
          ‖smoothSobolev (smoothCoordinateDerivative f i)‖) :=
      mul_le_mul_of_nonneg_left
        (norm_smoothHalfTrace_le hF hO hD τ0 (smoothCoordinateDerivative f i)) (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single i 1)).opNorm_nonneg
    _ ≤ ‖sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)‖ *
        (Real.sqrt (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass) *
          (‖unitBallCoordinateDerivativeL hcalc 1 i‖*‖smoothBallSobolev 2 f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (norm_smoothCoordinateDerivative_smoothSobolev_le hcalc f i) (Real.sqrt_nonneg _))
          (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single i 1)).opNorm_nonneg
    _ = _ := by ring

end OAI.AnisotropicCalderon.NativeSmoothHalfRadialTrace

#print axioms OAI.AnisotropicCalderon.NativeSmoothHalfRadialTrace.sphereSobolevInclusionL_smoothHalfTrace
#print axioms OAI.AnisotropicCalderon.NativeSmoothHalfRadialTrace.smoothHalfOutwardTrace
#print axioms OAI.AnisotropicCalderon.NativeSmoothHalfRadialTrace.sphereSobolevInclusionL_smoothHalfOutwardTrace
#print axioms OAI.AnisotropicCalderon.NativeSmoothHalfRadialTrace.norm_smoothCoordinateDerivative_smoothSobolev_le
#print axioms OAI.AnisotropicCalderon.NativeSmoothHalfRadialTrace.norm_smoothHalfOutwardTrace_le
