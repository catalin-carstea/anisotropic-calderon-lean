import Calderon.NativeFiniteHarmonicProductHighRotationGraph
import Calderon.SphereSobolevTangentialEndpointCompatibility

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-FINITE-PRODUCT-HIGH-TANGENTIAL-EXPANSION-v001.md. Actual tangential derivative after product. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] nativeFiniteHarmonicProductHighRotationL sphereSobolevLinearCoordinateMulL
  nativeThreeHalfCoefficientMulL sphereThreeHalfTangentialDerivativeL

def nativeFiniteHarmonicProductHighTangentialL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  ∑ j : Fin 3, (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
    (nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n Q j i)

lemma sphereSobolevInclusionL_nativeFiniteHarmonicProductHighTangentialL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (i : Fin 3) (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeFiniteHarmonicProductHighTangentialL hcalc hF hO hD τ0 n Q i f) =
      sphereThreeHalfTangentialDerivativeL hF hO hD i
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q (sphereSobolevPartialSum (3/2 : ℝ) n f)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let u := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q (sphereSobolevPartialSum (3/2 : ℝ) n f)
  have hTerm (j : Fin 3) :
      I (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
        (nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n Q j i f)) =
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
        (sphereSobolevRotationL (3/2 : ℝ) j i u) :=
    (sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (EuclideanSpace.single j 1) _).trans
      (congrArg (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1))
        (sphereSobolevInclusionL_nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n Q j i f))
  simp only [nativeFiniteHarmonicProductHighTangentialL,sphereThreeHalfTangentialDerivativeL,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
  exact Finset.sum_congr rfl (fun j _ => hTerm j)

lemma contDiff_nativeFiniteHarmonicProductHighTangentialL_of_value_graph
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (i : Fin 3) (m : P × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → m (p,x)=0)
    (Q : P → SmoothCoefficientJets 3) (hQ : ∀ p, coefficientValue 3 (Q p) = fun x => m (p,x)) :
    ContDiff ℝ ∞ (fun p => nativeFiniteHarmonicProductHighTangentialL hcalc hF hO hD τ0 n (Q p) i) := by
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.clm_comp
    (contDiff_nativeFiniteHarmonicProductHighRotationL_of_value_graph hcalc hF hO hD τ0 n j i m hm K hK hz Q hQ)

end OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion

#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.nativeFiniteHarmonicProductHighTangentialL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.sphereSobolevInclusionL_nativeFiniteHarmonicProductHighTangentialL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.contDiff_nativeFiniteHarmonicProductHighTangentialL_of_value_graph
