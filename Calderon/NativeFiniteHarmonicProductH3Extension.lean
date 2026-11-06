import Calderon.NativeFiniteHarmonicH3Extension
import Calderon.NativeThreeHalfProductTrace
import Calderon.NativeRepackedCoefficientMultiplierTopology

/-! H3 extension of the finite harmonic product: the untruncated actual multiplier on finite
input. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH2ThreeHalfValueTrace NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] coefficientMultiplier harmonicNativeH3PartialLiftL harmonicLiftCompletion
  nativeThreeHalfValueTraceL nativeThreeHalfCoefficientMulL

def nativeFiniteHarmonicProductLiftL (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (n : ℕ) (Q : SmoothCoefficientJets 3) : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 3 :=
  (coefficientMultiplier hcalc 3 (coefficientRepackedJets 3 4 Q)).comp
    (harmonicNativeH3PartialLiftL hF n)

lemma lowerOrder_nativeFiniteHarmonicProductLiftL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)) :
    TauCeti.Wkp.lowerOrder 2 (nativeFiniteHarmonicProductLiftL hcalc hF n Q f) =
      coefficientMultiplier hcalc 2 Q
        (harmonicLiftCompletion hF (sphereSobolevPartialSum (3/2 : ℝ) n f)) :=
  (lowerOrder_coefficientMultiplier_of_value_eq hcalc 2 (coefficientRepackedJets 3 4 Q) Q
    (coefficientValue_repackedJets 3 4 Q) (harmonicNativeH3PartialLiftL hF n f)).trans
    (congrArg (coefficientMultiplier hcalc 2 Q) (lowerOrder_harmonicNativeH3PartialLiftL hF hO n f))

lemma nativeThreeHalfValueTraceL_lowerOrder_nativeFiniteHarmonicProductLiftL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)) :
    nativeThreeHalfValueTraceL hcalc hF hO hD τ0
      (TauCeti.Wkp.lowerOrder 2 (nativeFiniteHarmonicProductLiftL hcalc hF n Q f)) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q (sphereSobolevPartialSum (3/2 : ℝ) n f) :=
  (congrArg (nativeThreeHalfValueTraceL hcalc hF hO hD τ0)
    (lowerOrder_nativeFiniteHarmonicProductLiftL hcalc hF hO n Q f)).trans
    ((nativeThreeHalfValueTraceL_coefficientMultiplier hcalc hF hO hD τ0 Q _).trans
      (congrArg (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q)
        (nativeThreeHalfValueTraceL_harmonicLiftCompletion hcalc hF hO hD τ0 _)))

lemma contDiff_nativeFiniteHarmonicProductLiftL_of_value_graph
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (n : ℕ)
    (m : P × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ p x, x ∉ K → m (p,x)=0) (Q : P → SmoothCoefficientJets 3)
    (hQ : ∀ p, coefficientValue 3 (Q p) = fun x => m (p,x)) :
    ContDiff ℝ ∞ (fun p => nativeFiniteHarmonicProductLiftL hcalc hF n (Q p)) :=
  (contDiff_repackedCoefficientMultiplier_of_value_graph hcalc 3 3 m hm K hK hz Q hQ).clm_comp
    contDiff_const

end OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion

#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.nativeFiniteHarmonicProductLiftL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.lowerOrder_nativeFiniteHarmonicProductLiftL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.nativeThreeHalfValueTraceL_lowerOrder_nativeFiniteHarmonicProductLiftL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.contDiff_nativeFiniteHarmonicProductLiftL_of_value_graph
