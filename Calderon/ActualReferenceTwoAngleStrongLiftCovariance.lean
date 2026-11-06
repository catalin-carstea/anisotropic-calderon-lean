import Calderon.ActualReferenceTwoAngleStrongWeakIdentification
import Calderon.NativeH2OutwardTraceOrthogonalCovariance

/-! Actual uncompressed outer covariance. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
open SmoothSphereRotation NativeFullHalfRadialTrace
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma firstOrder_referenceRotationHarmonicLiftFamily_eq_nativeWeakHalfLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (k l : Fin 3) (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (hStrong : (referenceRotationStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    TauCeti.Wkp.firstOrder 1 (referenceRotationHarmonicLiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) (harmonicLiftCompletion hF f)) =
    referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF k l (φ,p)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  let f0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let U : BallH1 := TauCeti.Wkp.firstOrder 1 (referenceRotationHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) (harmonicLiftCompletion hF f))
  let V : BallH1 := referenceRotationNativeWeakHalfLiftFamily
    g L y0 Φ B ε C ρ H a w hData hF k l (φ,p) f0
  let E0 : BallH1 := harmonicFirstOrderLiftCompletion hF f0
  have hU : E0-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceRotationHarmonicLiftFamily_half_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO k l (φ,p) hStrong f
  have hV : E0-V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    nativeWeakHalfLift_affine_difference
      (fun x => coordinateRotationPrincipalFamily k l a ((φ,p),x))
      (fun x => coordinateRotationDriftFamily k l
        (conformalReferenceWeightedFramedDrift g L Φ H w) ((φ,p),x)) 0
      (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData k l (φ,p)) hF f0
  have hz := sub_mem_nativeZero_of_common_difference E0 U V hU hV
  have hActual := referenceRotationWeakDirichletEnergyFamily_isInvertible_of_original
    g L y0 Φ B ε C ρ H a w hData hcalc k l φ p hOriginal
  have hEq := referenceRotationWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)
  have hNative := (nativeZeroCoefficientEnergyL_isInvertible_iff
    (fun x => coordinateRotationPrincipalFamily k l a ((φ,p),x))
    (fun x => coordinateRotationDriftFamily k l
      (conformalReferenceWeightedFramedDrift g L Φ H w) ((φ,p),x)) 0
    (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData k l (φ,p))).mp
      (Eq.mp (congrArg (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.IsInvertible) hEq) hActual)
  exact eq_of_native_weak_solution_of_isInvertible
    (fun x => coordinateRotationPrincipalFamily k l a ((φ,p),x))
    (fun x => coordinateRotationDriftFamily k l
      (conformalReferenceWeightedFramedDrift g L Φ H w) ((φ,p),x)) 0
    (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData k l (φ,p))
    hNative U V hz
    (fun v => referenceRotationHarmonicLiftFamily_weak_energy
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) hStrong (harmonicLiftCompletion hF f) v)
    (fun v => referenceRotationNativeWeakHalfLiftFamily_weak_solution_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc hF k l φ p hOriginal f0 v)

lemma referenceTwoAngleHarmonicLiftFamily_outer_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (hInner : (referenceRotationStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)).IsInvertible)
    (hTwo : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    nativeH2OrthogonalPullback hcalc (coordinateRotationIsometry i j θ)
      (referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)
        (harmonicLiftCompletion hF f)) =
    referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))
      (harmonicLiftCompletion hF (sphereSobolevOrthogonalPullbackL (3/2:ℝ)
        (coordinateRotationIsometry i j θ) f)) := by
  let e := coordinateRotationIsometry i j θ
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let U3 := sphereSobolevOrthogonalPullbackL (3/2:ℝ) e
  let U1 := sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
  have hInc : I (U3 f) = U1 (I f) :=
    congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T f)
      (sphereSobolevInclusionL_orthogonalPullback (3/2:ℝ) (1/2:ℝ) (by norm_num) e)
  apply nativeH2_firstOrder_injective
  rw [firstOrder_nativeH2OrthogonalPullback]
  have hInnerGraph := firstOrder_referenceRotationHarmonicLiftFamily_eq_nativeWeakHalfLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO k l φ p hOriginal hInner f
  have hWeak := referenceTwoAngleNativeWeakHalfLiftFamily_outer_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j k l θ φ p hOriginal (I f)
  have hTwoGraph := firstOrder_referenceTwoAngleHarmonicLiftFamily_eq_nativeWeakHalfLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j k l (θ,(φ,p)) hOriginal hTwo (U3 f)
  exact (congrArg (nativeH1OrthogonalPullback e) hInnerGraph).trans
    (hWeak.trans ((congrArg (referenceTwoAngleNativeWeakHalfLiftFamily
      g L y0 Φ B ε C ρ H a w hData hF i j k l (θ,(φ,p))) hInc.symm).trans hTwoGraph.symm))

lemma referenceTwoAngleSharpRadialTraceFamily_outer_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (hInner : (referenceRotationStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)).IsInvertible)
    (hTwo : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceTwoAngleSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p))
      (sphereSobolevOrthogonalPullbackL (3/2:ℝ) (coordinateRotationIsometry i j θ) f) =
    sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ)
      (referenceRotationSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l (φ,p) f) := by
  have hH := referenceTwoAngleHarmonicLiftFamily_outer_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j k l θ φ p hOriginal hInner hTwo f
  have hTrace := congrArg (nativeHalfOutwardTraceL hF hO hD hcalc τ0) hH
  have hCov := nativeHalfOutwardTraceL_nativeH2OrthogonalPullback
    hF hO hD hcalc τ0 (coordinateRotationIsometry i j θ)
      (referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)
        (harmonicLiftCompletion hF f))
  exact hTrace.symm.trans hCov

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_referenceRotationHarmonicLiftFamily_eq_nativeWeakHalfLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleHarmonicLiftFamily_outer_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSharpRadialTraceFamily_outer_covariance
