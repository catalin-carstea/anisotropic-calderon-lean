import Calderon.NativeFiniteHarmonicProductH3Extension
import Calderon.NativeH3RotationEndpointGraph

/-! Rotation after the actual untruncated product. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH3FiveHalfValueTrace NativeH2ThreeHalfValueTrace NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] nativeFiniteHarmonicProductLiftL nativeH3ThreeHalfRotationTraceL
  nativeThreeHalfValueTraceL nativeThreeHalfCoefficientMulL sphereSobolevRotationL

def nativeFiniteHarmonicProductHighRotationL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (i j : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  (nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j).comp
    (nativeFiniteHarmonicProductLiftL hcalc hF n Q)

lemma sphereSobolevInclusionL_nativeFiniteHarmonicProductHighRotationL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (i j : Fin 3) (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n Q i j f) =
      sphereSobolevRotationL (3/2 : ℝ) i j
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q (sphereSobolevPartialSum (3/2 : ℝ) n f)) :=
  (nativeH3ThreeHalfRotationTraceL_endpoint_graph hcalc hF hO hD τ0 i j
    (nativeFiniteHarmonicProductLiftL hcalc hF n Q f)).trans
    (congrArg (sphereSobolevRotationL (3/2 : ℝ) i j)
      (nativeThreeHalfValueTraceL_lowerOrder_nativeFiniteHarmonicProductLiftL hcalc hF hO hD τ0 n Q f))

lemma contDiff_nativeFiniteHarmonicProductHighRotationL_of_value_graph
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (i j : Fin 3) (m : P × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → m (p,x)=0)
    (Q : P → SmoothCoefficientJets 3) (hQ : ∀ p, coefficientValue 3 (Q p) = fun x => m (p,x)) :
    ContDiff ℝ ∞ (fun p => nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n (Q p) i j) :=
  contDiff_const.clm_comp
    (contDiff_nativeFiniteHarmonicProductLiftL_of_value_graph hcalc hF n m hm K hK hz Q hQ)

end OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion

#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.nativeFiniteHarmonicProductHighRotationL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.sphereSobolevInclusionL_nativeFiniteHarmonicProductHighRotationL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.contDiff_nativeFiniteHarmonicProductHighRotationL_of_value_graph
