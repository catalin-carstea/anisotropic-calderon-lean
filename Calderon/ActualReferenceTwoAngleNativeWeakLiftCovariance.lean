import Calderon.ActualReferenceTwoAngleNativeWeakHalfLiftCore
import Calderon.ActualReferenceRotationWeakHalfLiftTopology
import Calderon.NativeWeakHalfLiftOrthogonalCovariance
import Mathlib.Tactic.Abel

/-! Actual weak uniqueness and the same zero correction identify uncompressed
native lifts; no covariance premise. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open SphereHarmonic NativeHarmonicH1LiftCompletion SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma referenceTwoAngleNativeZeroEnergy_isInvertible_of_original
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible) :
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (b := fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) (c := 0)
      (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t)).IsInvertible := by
  have hActual := referenceTwoAngleWeakDirichletEnergyFamily_isInvertible_of_original
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t.1 t.2.1 t.2.2 hOriginal
  have hEq := referenceTwoAngleWeakDirichletEnergyFamily_eq_nativeZeroEnergy
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
  apply (nativeZeroCoefficientEnergyL_isInvertible_iff
    (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
    (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t)).mp
  exact Eq.mp (congrArg (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.IsInvertible) hEq) hActual

lemma referenceRotationNativeWeakHalfLiftFamily_weak_solution_of_original
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (k l : Fin 3)
    (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => coordinateRotationPrincipalFamily k l a ((φ,p),x))
      (fun x => coordinateRotationDriftFamily k l
        (conformalReferenceWeightedFramedDrift g L Φ H w) ((φ,p),x)) 0
      (referenceRotationNativeWeakHalfLiftFamily
        g L y0 Φ B ε C ρ H a w hData hF k l (φ,p) f) (v : BallH1) = 0 := by
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
  exact nativeWeakHalfLift_weak_solution
    (fun x => coordinateRotationPrincipalFamily k l a ((φ,p),x))
    (fun x => coordinateRotationDriftFamily k l
      (conformalReferenceWeightedFramedDrift g L Φ H w) ((φ,p),x)) 0
    (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData k l (φ,p)) hF hNative f v

lemma referenceTwoAngleNativeWeakHalfLiftFamily_outer_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) :
    nativeH1OrthogonalPullback (coordinateRotationIsometry i j θ)
      (referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF k l (φ,p) f) =
    referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l (θ,(φ,p))
      (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) (coordinateRotationIsometry i j θ) f) := by
  let e := coordinateRotationIsometry i j θ
  let f' := sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e f
  let W := referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF k l (φ,p)
  let U : BallH1 := nativeH1OrthogonalPullback e (W f)
  let V : BallH1 := referenceTwoAngleNativeWeakHalfLiftFamily
    g L y0 Φ B ε C ρ H a w hData hF i j k l (θ,(φ,p)) f'
  let E0 : BallH1 := harmonicFirstOrderLiftCompletion hF f'
  have hEU : E0-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    have hOld := nativeWeakHalfLift_affine_difference
      (fun x => coordinateRotationPrincipalFamily k l a ((φ,p),x))
      (fun x => coordinateRotationDriftFamily k l
        (conformalReferenceWeightedFramedDrift g L Φ H w) ((φ,p),x)) 0
      (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData k l (φ,p)) hF f
    have h := nativeH1OrthogonalPullback_affine_difference e
      (harmonicFirstOrderLiftCompletion hF f) (W f) hOld
    rw [harmonicFirstOrderLiftCompletion_orthogonalPullback hF hO] at h
    exact h
  have hEV : E0-V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceTwoAngleNativeWeakHalfLiftFamily_affine_difference
      g L y0 Φ B ε C ρ H a w hData hF i j k l (θ,(φ,p)) f'
  have hUV : U-V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    have h : U-V = (E0-V)-(E0-U) := by abel
    exact h.symm ▸ (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).sub_mem hEV hEU
  apply eq_of_native_weak_solution_of_isInvertible
    (fun x => referenceTwoAnglePrincipalFamily a i j k l ((θ,(φ,p)),x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l ((θ,(φ,p)),x)) 0
    (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l (θ,(φ,p)))
    (referenceTwoAngleNativeZeroEnergy_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p)) hOriginal) U V hUV
  · intro v
    have hBack : nativeH1OrthogonalPullback e
        (nativeH1OrthogonalPullback e.symm (v : BallH1)) = (v : BallH1) := by
      simpa only [LinearIsometryEquiv.symm_symm] using
        nativeH1OrthogonalPullback_symm_apply e.symm (v : BallH1)
    let F : BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
      referenceTwoAngleFullWeakEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))
    let A : BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
      referenceRotationFullWeakEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)
    have hCov : F U (nativeH1OrthogonalPullback e
        (nativeH1OrthogonalPullback e.symm (v : BallH1))) =
        A (W f) (nativeH1OrthogonalPullback e.symm (v : BallH1)) :=
      referenceTwoAngleFullWeakEnergyFamily_outer_covariance
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l θ φ p (W f)
          (nativeH1OrthogonalPullback e.symm (v : BallH1))
    have hTest : F U (nativeH1OrthogonalPullback e
        (nativeH1OrthogonalPullback e.symm (v : BallH1))) = F U (v : BallH1) :=
      congrArg (fun z : BallH1 => F U z) hBack
    have hInner := referenceRotationNativeWeakHalfLiftFamily_weak_solution_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc hF k l φ p hOriginal f
        (nativeH1ZeroOrthogonalPullback e.symm v)
    have hRight := (referenceRotationFullWeakEnergyFamily_apply
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) (W f)
        (nativeH1OrthogonalPullback e.symm (v : BallH1))).trans hInner
    exact (referenceTwoAngleFullWeakEnergyFamily_apply
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p)) U (v : BallH1)).symm.trans
        (hTest.symm.trans (hCov.trans hRight))
  · intro v
    exact referenceTwoAngleNativeWeakHalfLiftFamily_weak_solution
      g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l (θ,(φ,p)) hOriginal f' v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNativeZeroEnergy_isInvertible_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNativeWeakHalfLiftFamily_weak_solution_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNativeWeakHalfLiftFamily_outer_covariance
