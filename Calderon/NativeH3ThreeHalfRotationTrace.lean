import Calderon.NativeSobolevCoordinateDerivativeCoherence
import Calderon.NativeThreeHalfCoefficientMultiplier

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-H3-TRACE-EXPANSION-v001.md, Component C. Same native derivative and coarse rotation graph. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  SpectralCoreRegularity NativeH2ThreeHalfValueTrace NativeThreeHalfCoefficientMultiplier

def nativeH3ThreeHalfRotationTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) : BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)).comp
    ((nativeThreeHalfValueTraceL hcalc hF hO hD τ0).comp (unitBallCoordinateDerivativeL hcalc 2 j)) -
  (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
    ((nativeThreeHalfValueTraceL hcalc hF hO hD τ0).comp (unitBallCoordinateDerivativeL hcalc 2 i))

lemma nativeH3ThreeHalfRotationTraceL_apply (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) (U : BallSobolev 3) :
    nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U =
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (unitBallCoordinateDerivativeL hcalc 2 j U)) -
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (unitBallCoordinateDerivativeL hcalc 2 i U)) := rfl

attribute [local irreducible] nativeThreeHalfValueTraceL sphereSobolevLinearCoordinateMulL
  unitBallCoordinateDerivativeL sphereSobolevInclusionL

lemma sphereSobolevInclusionL_nativeH3ThreeHalfRotationTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) (U : BallSobolev 3) :
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
      (nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U) =
      sphereSobolevZeroEquiv hO hD
        (sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j (TauCeti.Wkp.lowerOrder 2 U)) -
          sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i (TauCeti.Wkp.lowerOrder 2 U))) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let d (a : Fin 3) := unitBallCoordinateDerivativeL hcalc 2 a U
  let T := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let M (a : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single a 1)
  let t (a : Fin 3) := strongCoordinateTraceL hcalc τ0 a (TauCeti.Wkp.lowerOrder 2 U)
  have hTrace (a : Fin 3) : I (T (d a)) = Z (t a) := by
    have hHigh := sphereSobolevInclusionL_nativeThreeHalfValueTraceL_zero hcalc hF hO hD τ0 (d a)
    have hSame := congrArg (fun W : BallH1 => Z (τ0.valueTraceL W))
      (firstOrder_unitBallCoordinateDerivativeL_H3 hcalc a U)
    exact hHigh.trans hSame
  have hTerm (a b : Fin 3) : I (M a (T (d b))) = Z (sphereCoordinateMulL a (t b)) := by
    have h := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD (3/2 : ℝ)
      (by norm_num) (EuclideanSpace.single a 1) (T (d b)) (t b) (hTrace b)
    simpa only [I,Z,M,sphereLinearCoordinateMulL_single] using h
  have hPoint := congrArg I (nativeH3ThreeHalfRotationTraceL_apply hcalc hF hO hD τ0 i j U)
  have hSub := I.map_sub (M i (T (d j))) (M j (T (d i)))
  exact hPoint.trans (hSub.trans ((congrArg₂ (fun x y : SphereSobolev 0 => x-y)
    (hTerm i j) (hTerm j i)).trans (Z.map_sub _ _).symm))

lemma sphereSobolevCoefficientL_nativeH3ThreeHalfRotationTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) (U : BallSobolev 3) (k : ℕ) :
    sphereSobolevCoefficientL (3/2 : ℝ) k (nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U) =
      SmoothSphereRotationProjection.harmonicSphereRotation k i j
        (sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (TauCeti.Wkp.firstOrder 2 U))) := by
  have h := congrArg (sphereSobolevCoefficientL 0 k)
    (sphereSobolevInclusionL_nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U)
  simp only [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv] at h
  have hRotation := sphereHarmonicCoordinate_nativeH2_rotation
    hcalc hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U) k j i
  exact h.trans hRotation

lemma nativeH3ThreeHalfRotationTraceL_storedGraph (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) (U : BallSobolev 3) (k : ℕ) :
    nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U k =
      SmoothSphereRotationProjection.harmonicSphereRotation k i j
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U) k) := by
  let V := nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U
  let W := nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (TauCeti.Wkp.lowerOrder 2 U)
  let A := SmoothSphereRotationProjection.harmonicSphereRotation k i j
  have hCoeff : sphereSobolevCoefficientL (3/2 : ℝ) k W =
      sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (TauCeti.Wkp.firstOrder 2 U)) := by
    simpa only [TauCeti.Wkp.firstOrder_succ] using
      (sphereSobolevCoefficientL_nativeThreeHalfValueTraceL hcalc hF hO hD τ0
        (TauCeti.Wkp.lowerOrder 2 U) k)
  have hDecoded : sphereSobolevCoefficientL (3/2 : ℝ) k V =
      A (sphereSobolevCoefficientL (3/2 : ℝ) k W) :=
    (sphereSobolevCoefficientL_nativeH3ThreeHalfRotationTraceL hcalc hF hO hD τ0 i j U k).trans
      (congrArg A hCoeff.symm)
  calc
    V k = SpectralWeightedGraph.besselWeight (3/2 : ℝ) k •
        sphereSobolevCoefficientL (3/2 : ℝ) k V :=
      (sphereSobolevCoefficientL_reconstruct (3/2 : ℝ) k V).symm
    _ = SpectralWeightedGraph.besselWeight (3/2 : ℝ) k •
        A (sphereSobolevCoefficientL (3/2 : ℝ) k W) :=
      congrArg (fun z : harmonicSphereSubspace k =>
        SpectralWeightedGraph.besselWeight (3/2 : ℝ) k • z) hDecoded
    _ = A (SpectralWeightedGraph.besselWeight (3/2 : ℝ) k •
        sphereSobolevCoefficientL (3/2 : ℝ) k W) := (map_smul A _ _).symm
    _ = A (W k) := congrArg A (sphereSobolevCoefficientL_reconstruct (3/2 : ℝ) k W)

end OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace

#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.nativeH3ThreeHalfRotationTraceL
#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.nativeH3ThreeHalfRotationTraceL_apply
#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.sphereSobolevInclusionL_nativeH3ThreeHalfRotationTraceL
#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.sphereSobolevCoefficientL_nativeH3ThreeHalfRotationTraceL
#print axioms OAI.AnisotropicCalderon.NativeH3FiveHalfValueTrace.nativeH3ThreeHalfRotationTraceL_storedGraph
