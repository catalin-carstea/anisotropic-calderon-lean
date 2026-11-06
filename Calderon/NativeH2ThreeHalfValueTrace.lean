import Calderon.SphereSobolevTraceReconstruction
import Calderon.NativeSupportedAdjointStrongForcing
import Calderon.NativeH2RotationTrace
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.NativeHarmonicLiftOrderCoherence
import Calderon.NativeHarmonicH1LiftTraceCompatibility

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  SpectralCoreRegularity NativeFullSharpHalfTrace NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
  NativeHarmonicH1LiftTraceCompatibility

def nativeH2HalfRotationTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) : BallSobolev 2 →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (sphereSobolevLinearCoordinateMulL hF hO hD (1/2:ℝ) (EuclideanSpace.single i 1)).comp
    ((nativeHalfTraceL hF hO hD τ0).comp
      ((TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0).comp
        (unitBallCoordinateDerivativeL hcalc 1 j))) -
  (sphereSobolevLinearCoordinateMulL hF hO hD (1/2:ℝ) (EuclideanSpace.single j 1)).comp
    ((nativeHalfTraceL hF hO hD τ0).comp
      ((TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0).comp
        (unitBallCoordinateDerivativeL hcalc 1 i)))

lemma nativeH2HalfRotationTraceL_apply (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) (U : BallSobolev 2) :
    nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U =
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2:ℝ) (EuclideanSpace.single i 1)
        (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 j U))) -
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2:ℝ) (EuclideanSpace.single j 1)
        (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U))) := rfl

lemma sphereSobolevInclusionL_nativeH2HalfRotationTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) (U : BallSobolev 2) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U) =
      sphereSobolevZeroEquiv hO hD
        (sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j U) -
          sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i U)) := by
  let I : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let d (l : Fin 3) : BallH1 := TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 l U)
  let C (l : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (1/2:ℝ) (EuclideanSpace.single l 1)
  have hTerm (l m : Fin 3) : I (C l (nativeHalfTraceL hF hO hD τ0 (d m))) =
      Z (sphereCoordinateMulL l (τ0.valueTraceL (d m))) := by
    have h := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD (1/2:ℝ)
      (by norm_num) (EuclideanSpace.single l 1) (nativeHalfTraceL hF hO hD τ0 (d m))
      (τ0.valueTraceL (d m)) (sphereSobolevInclusionL_nativeHalfTraceL hF hO hD τ0 (d m))
    simpa only [I,Z,C,sphereLinearCoordinateMulL_single] using h
  have hPoint := congrArg I (nativeH2HalfRotationTraceL_apply hcalc hF hO hD τ0 i j U)
  have hSub := I.map_sub (C i (nativeHalfTraceL hF hO hD τ0 (d j)))
    (C j (nativeHalfTraceL hF hO hD τ0 (d i)))
  exact hPoint.trans (hSub.trans ((congrArg₂ (fun x y : SphereSobolev 0 => x-y)
    (hTerm i j) (hTerm j i)).trans (Z.map_sub _ _).symm))

lemma sphereSobolevCoefficientL_nativeH2HalfRotationTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) (U : BallSobolev 2) (k : ℕ) :
    sphereSobolevCoefficientL (1/2:ℝ) k (nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U) =
      SmoothSphereRotationProjection.harmonicSphereRotation k i j
        (sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U))) := by
  have h := congrArg (sphereSobolevCoefficientL 0 k)
    (sphereSobolevInclusionL_nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U)
  simp only [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv] at h
  exact h.trans (sphereHarmonicCoordinate_nativeH2_rotation hcalc hO hD τ0 U k j i)

lemma nativeH2HalfRotationTraceL_storedGraph (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) (U : BallSobolev 2) (k : ℕ) :
    nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U k =
      SmoothSphereRotationProjection.harmonicSphereRotation k i j
        (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) k) := by
  rw [← sphereSobolevCoefficientL_reconstruct (1/2:ℝ) k
    (nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U)]
  rw [sphereSobolevCoefficientL_nativeH2HalfRotationTraceL,
    ← sphereSobolevCoefficientL_nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) k,
    ← map_smul,sphereSobolevCoefficientL_reconstruct]

def nativeThreeHalfValueTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) : BallSobolev 2 →L[ℝ] SphereSobolev (3/2:ℝ) :=
  sphereSobolevTraceReconstructionIdentityL.comp ((nativeHalfTraceL hF hO hD τ0).comp nativeH2FirstOrderL) +
    ∑ i : Fin 3, ∑ j : Fin 3, (sphereSobolevTraceReconstructionRotationL i j).comp
      (nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j)

lemma sphereSobolevCoefficientL_nativeThreeHalfValueTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 2) (k : ℕ) :
    sphereSobolevCoefficientL (3/2:ℝ) k (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 U) =
      sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)) := by
  have hPoint : nativeThreeHalfValueTraceL hcalc hF hO hD τ0 U =
      sphereSobolevTraceReconstructionIdentityL (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)) +
      ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j
        (nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U) := by
    have hRaw : nativeThreeHalfValueTraceL hcalc hF hO hD τ0 U =
        sphereSobolevTraceReconstructionIdentityL (nativeHalfTraceL hF hO hD τ0 (nativeH2FirstOrderL U)) +
        ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j
          (nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U) := by
      simp only [nativeThreeHalfValueTraceL,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.comp_apply]
    have hFirst : nativeH2FirstOrderL U = TauCeti.Wkp.firstOrder 1 U := nativeH2FirstOrderL_apply U
    exact hRaw.trans (congrArg (fun z : BallH1 =>
      sphereSobolevTraceReconstructionIdentityL (nativeHalfTraceL hF hO hD τ0 z) +
        ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j
          (nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U)) hFirst)
  have hRecon := sphereSobolevCoefficientL_traceReconstruction
    (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U))
    (fun i j => nativeH2HalfRotationTraceL hcalc hF hO hD τ0 i j U)
    (fun i j k => nativeH2HalfRotationTraceL_storedGraph hcalc hF hO hD τ0 i j U k) k
  exact (congrArg (sphereSobolevCoefficientL (3/2:ℝ) k) hPoint).trans
    (hRecon.trans (sphereSobolevCoefficientL_nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) k))

lemma sphereSobolevInclusionL_nativeThreeHalfValueTraceL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 2) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 U) =
      nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) := by
  apply sphereSobolev_ext (1/2:ℝ)
  intro k
  rw [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_nativeThreeHalfValueTraceL,
    sphereSobolevCoefficientL_nativeHalfTraceL]

lemma nativeThreeHalfValueTraceL_harmonicLiftCompletion (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (f : SphereSobolev (3/2:ℝ)) :
    nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (harmonicLiftCompletion hF f) = f := by
  apply sphereSobolev_ext (3/2:ℝ)
  intro k
  have hFirstL : TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 1 (harmonicLiftCompletion hF f) =
      TauCeti.Wkp.firstOrder 1 (harmonicLiftCompletion hF f) := rfl
  have hFirst : TauCeti.Wkp.firstOrder 1 (harmonicLiftCompletion hF f) =
      harmonicFirstOrderLiftCompletion hF
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) :=
    hFirstL.symm.trans (firstOrder_harmonicLiftCompletion hF hO f)
  have hTrace := congrArg (fun z : BallH1 => sphereHarmonicCoordinate hO hD k (τ0.valueTraceL z)) hFirst
  have hHalf := sphereHarmonicCoordinate_valueTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0 k
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
  exact (sphereSobolevCoefficientL_nativeThreeHalfValueTraceL hcalc hF hO hD τ0
    (harmonicLiftCompletion hF f) k).trans
    (hTrace.trans (hHalf.trans (sphereSobolevCoefficientL_inclusion (3/2:ℝ) (1/2:ℝ) (by norm_num) f k)))

end OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace

#print axioms OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace.nativeH2HalfRotationTraceL

#print axioms OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace.nativeH2HalfRotationTraceL_apply

#print axioms OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace.sphereSobolevInclusionL_nativeH2HalfRotationTraceL

#print axioms OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace.sphereSobolevCoefficientL_nativeH2HalfRotationTraceL

#print axioms OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace.nativeH2HalfRotationTraceL_storedGraph

#print axioms OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace.nativeThreeHalfValueTraceL

#print axioms OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace.sphereSobolevCoefficientL_nativeThreeHalfValueTraceL

#print axioms OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace.sphereSobolevInclusionL_nativeThreeHalfValueTraceL

#print axioms OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace.nativeThreeHalfValueTraceL_harmonicLiftCompletion
