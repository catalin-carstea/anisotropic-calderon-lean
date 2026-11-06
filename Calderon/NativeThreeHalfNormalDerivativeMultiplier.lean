import Calderon.NativeCoefficientMultiplierOrderCoherence
import Calderon.NativeH2SmoothMultiplierOutwardTrace
import Calderon.NativeOrderOneCoefficientMultiplier

/-! Genuine plus normal term at high endpoint. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier

def nativeThreeHalfNormalDerivativeMulL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  ∑ i : Fin 3, (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
    (EuclideanSpace.single i 1)).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (coefficientRepackedJets 2 3 (smoothMultiplierDerivativeJets Q i)))

lemma nativeThreeHalfNormalDerivativeMulL_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)) :
    nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q f =
      ∑ i : Fin 3, sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
          (coefficientRepackedJets 2 3 (smoothMultiplierDerivativeJets Q i)) f) := by
  simp only [nativeThreeHalfNormalDerivativeMulL,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]

attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  sphereSobolevLinearCoordinateMulL sphereSobolevInclusionL

lemma sphereSobolevInclusionL_nativeThreeHalfNormalDerivativeMulL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q f) =
    nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Mh (i : Fin 3) := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (coefficientRepackedJets 2 3 (smoothMultiplierDerivativeJets Q i))
  let Ml (i : Fin 3) := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierDerivativeJets Q i)
  let Ch (i : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)
  let Cl (i : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)
  have hM (i : Fin 3) : I (Mh i f) = Ml i (I f) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A f)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0
        (coefficientRepackedJets 2 3 (smoothMultiplierDerivativeJets Q i))
        (smoothMultiplierDerivativeJets Q i)
        (coefficientValue_repackedJets 2 3 (smoothMultiplierDerivativeJets Q i)))
  have hTerm (i : Fin 3) : I (Ch i (Mh i f)) = Cl i (Ml i (I f)) :=
    (sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (EuclideanSpace.single i 1) (Mh i f)).trans (congrArg (Cl i) (hM i))
  rw [nativeThreeHalfNormalDerivativeMulL_apply]
  change I (∑ i : Fin 3, Ch i (Mh i f)) = _
  rw [map_sum]
  have hLow : nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q (I f) =
      ∑ i : Fin 3, Cl i (Ml i (I f)) := by
    simp only [nativeHalfNormalDerivativeMulL,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply,Cl,Ml]
  exact (Finset.sum_congr rfl (fun i _ => hTerm i)).trans hLow.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeThreeHalfNormalDerivativeMulL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeThreeHalfNormalDerivativeMulL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_nativeThreeHalfNormalDerivativeMulL

