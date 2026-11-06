import Calderon.NativeLowerOrderProjection
import Calderon.SharpRadialHarmonicCoefficientCore
import Calderon.NativeH2ThreeHalfValueTrace

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-FINITE-HARMONIC-H3-EXTENSION-EXPANSION-v001.md. Fixed-cutoff native extension, no uniform cutoff bound. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  SphereHilbertDecomposition NativeH2ThreeHalfValueTrace

def harmonicNativeH3BlockL (hF : SphereFischerInner) (k : ℕ) :
    harmonicSphereSubspace k →L[ℝ] BallSobolev 3 := by
  letI := finiteDimensional_harmonicSphereSubspace k
  exact ((polynomialBallSobolevLinearMap 3).comp (harmonicPolynomialRepresentativeL hF k)).toContinuousLinearMap

lemma harmonicNativeH3BlockL_apply (hF : SphereFischerInner) (k : ℕ)
    (a : harmonicSphereSubspace k) :
    harmonicNativeH3BlockL hF k a = polynomialBallSobolev 3 (harmonicPolynomialRepresentativeL hF k a) := rfl

attribute [local irreducible] harmonicNativeH3BlockL harmonicLiftCompletion nativeThreeHalfValueTraceL
  nativeLowerOrderL

def harmonicNativeH3PartialLiftL (hF : SphereFischerInner) (n : ℕ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 3 :=
  ∑ k ∈ Finset.range n, (harmonicNativeH3BlockL hF k).comp (sphereSobolevCoefficientL (3/2 : ℝ) k)

lemma lowerOrder_harmonicNativeH3PartialLiftL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (n : ℕ)
    (f : SphereSobolev (3/2 : ℝ)) :
    TauCeti.Wkp.lowerOrder 2 (harmonicNativeH3PartialLiftL hF n f) =
      harmonicLiftCompletion hF (sphereSobolevPartialSum (3/2 : ℝ) n f) := by
  have hBlock (k : ℕ) (a : harmonicSphereSubspace k) :
      TauCeti.Wkp.lowerOrder 2 (harmonicNativeH3BlockL hF k a) =
        harmonicLiftCompletion hF (sphereSobolevSingleL (3/2 : ℝ) k a) := by
    have hPolynomial : TauCeti.Wkp.lowerOrder 2
        (polynomialBallSobolev 3 (harmonicPolynomialRepresentativeL hF k a)) =
        polynomialBallSobolev 2 (harmonicPolynomialRepresentativeL hF k a) :=
      lowerOrder_smoothBallSobolev 2 (smoothPolynomialData (harmonicPolynomialRepresentativeL hF k a))
    exact (congrArg (TauCeti.Wkp.lowerOrder 2) (harmonicNativeH3BlockL_apply hF k a)).trans
      (hPolynomial.trans (harmonicLiftCompletion_sphereSobolevSingle hF hO k a).symm)
  have hPoint : harmonicNativeH3PartialLiftL hF n f =
      ∑ k ∈ Finset.range n, harmonicNativeH3BlockL hF k (sphereSobolevCoefficientL (3/2 : ℝ) k f) := by
    simp only [harmonicNativeH3PartialLiftL,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  have hLower := congrArg (TauCeti.Wkp.lowerOrder 2) hPoint
  have hSum := map_sum (nativeLowerOrderL 2)
    (fun k => harmonicNativeH3BlockL hF k (sphereSobolevCoefficientL (3/2 : ℝ) k f)) (Finset.range n)
  have hSum' : TauCeti.Wkp.lowerOrder 2
      (∑ k ∈ Finset.range n, harmonicNativeH3BlockL hF k (sphereSobolevCoefficientL (3/2 : ℝ) k f)) =
      ∑ k ∈ Finset.range n, TauCeti.Wkp.lowerOrder 2
        (harmonicNativeH3BlockL hF k (sphereSobolevCoefficientL (3/2 : ℝ) k f)) :=
    (nativeLowerOrderL_apply 2 _).symm.trans (hSum.trans
      (Finset.sum_congr rfl (fun k _ => nativeLowerOrderL_apply 2 _)))
  have hBlocks := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range n) =>
    hBlock k (sphereSobolevCoefficientL (3/2 : ℝ) k f))
  have hLiftSum : harmonicLiftCompletion hF (sphereSobolevPartialSum (3/2 : ℝ) n f) =
      ∑ k ∈ Finset.range n, harmonicLiftCompletion hF
        (sphereSobolevSingleL (3/2 : ℝ) k (sphereSobolevCoefficientL (3/2 : ℝ) k f)) := by
    simp only [sphereSobolevPartialSum,map_sum]
  exact hLower.trans (hSum'.trans (hBlocks.trans hLiftSum.symm))

lemma nativeThreeHalfValueTraceL_lowerOrder_harmonicNativeH3PartialLiftL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (f : SphereSobolev (3/2 : ℝ)) :
    nativeThreeHalfValueTraceL hcalc hF hO hD τ0
      (TauCeti.Wkp.lowerOrder 2 (harmonicNativeH3PartialLiftL hF n f)) =
      sphereSobolevPartialSum (3/2 : ℝ) n f :=
  (congrArg (nativeThreeHalfValueTraceL hcalc hF hO hD τ0)
    (lowerOrder_harmonicNativeH3PartialLiftL hF hO n f)).trans
      (nativeThreeHalfValueTraceL_harmonicLiftCompletion hcalc hF hO hD τ0 _)

end OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion

#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.harmonicNativeH3BlockL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.harmonicNativeH3BlockL_apply
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.harmonicNativeH3PartialLiftL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.lowerOrder_harmonicNativeH3PartialLiftL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.nativeThreeHalfValueTraceL_lowerOrder_harmonicNativeH3PartialLiftL
