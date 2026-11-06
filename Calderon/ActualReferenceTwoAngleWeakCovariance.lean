import Calderon.ActualReferenceTwoAngleWeakOperator
import Calderon.ActualReferenceRotationAdjointWeakZeroInverse
import Calderon.NativeContinuousCoefficientOrthogonalEnergy

/-! Tested covariance and inverse transport from the original weak inverse. -/
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

open SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

attribute [local irreducible] referenceTwoAngleFullWeakEnergyFamily
  referenceTwoAngleWeakEnergyFamily referenceTwoAngleWeakDirichletEnergyFamily
  referenceRotationFullWeakEnergyFamily referenceRotationWeakEnergyFamily
  referenceRotationWeakDirichletEnergyFamily referenceWeakDirichletEnergyFamily
  nativeH1OrthogonalPullback nativeH1ZeroOrthogonalPullback

set_option diagnostics true in
lemma referenceTwoAngleFullWeakEnergyFamily_outer_covariance
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (u v : BallH1) :
    referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))
      (nativeH1OrthogonalPullback (coordinateRotationIsometry i j θ) u)
      (nativeH1OrthogonalPullback (coordinateRotationIsometry i j θ) v) =
    referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) u v := by
  let e := coordinateRotationIsometry i j θ
  let a0 : MatrixField := fun x => coordinateRotationPrincipalFamily k l a ((φ,p),x)
  let b0 : R3 → R3 := fun x => coordinateRotationDriftFamily k l
    (conformalReferenceWeightedFramedDrift g L Φ H w) ((φ,p),x)
  have ha : Continuous a0 := (referenceRotationPrincipal_data
    g L y0 Φ B ε C ρ H a w hData k l).1.continuous.comp (continuous_const.prodMk continuous_id)
  have hb : Continuous b0 := (referenceRotationDrift_data
    g L y0 Φ B ε C ρ H a w hData k l).1.continuous.comp (continuous_const.prodMk continuous_id)
  have hA : (fun x => referenceTwoAnglePrincipalFamily a i j k l ((θ,(φ,p)),x)) =
      orthogonalPrincipalCoefficient e a0 := by
    funext x
    exact coordinateRotationPrincipalFamily_eq_orthogonal i j
      (coordinateRotationPrincipalFamily k l a) θ (φ,p) x
  have hB : (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l ((θ,(φ,p)),x)) =
      orthogonalDriftCoefficient e b0 := by
    funext x
    exact coordinateRotationDriftFamily_eq_orthogonal i j
      (coordinateRotationDriftFamily k l (conformalReferenceWeightedFramedDrift g L Φ H w)) θ (φ,p) x
  have hActual : referenceTwoAngleFullWeakEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))
        (nativeH1OrthogonalPullback e u) (nativeH1OrthogonalPullback e v) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referenceTwoAnglePrincipalFamily a i j k l ((θ,(φ,p)),x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l ((θ,(φ,p)),x)) 0
        (nativeH1OrthogonalPullback e u) (nativeH1OrthogonalPullback e v) :=
    referenceTwoAngleFullWeakEnergyFamily_apply
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))
        (nativeH1OrthogonalPullback e u) (nativeH1OrthogonalPullback e v)
  have hFields := congrArg₂
    (fun (A : MatrixField) (beta : R3 → R3) => TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) A beta 0
        (nativeH1OrthogonalPullback e u) (nativeH1OrthogonalPullback e v)) hA hB
  have hCov : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (orthogonalPrincipalCoefficient e a0) (orthogonalDriftCoefficient e b0) 0
        (nativeH1OrthogonalPullback e u) (nativeH1OrthogonalPullback e v) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a0 b0 0 u v :=
    energyFormH1_orthogonal_covariance e a0 b0 0 ha hb continuous_const u v
  have hInner : referenceRotationFullWeakEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a0 b0 0 u v :=
    referenceRotationFullWeakEnergyFamily_apply
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) u v
  exact hActual.trans (hFields.trans (hCov.trans hInner.symm))


lemma referenceTwoAngleWeakDirichletEnergyFamily_outer_covariance
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (u v : BallH1Zero) :
    referenceTwoAngleWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))
      (nativeH1ZeroOrthogonalPullback (coordinateRotationIsometry i j θ) u)
      (nativeH1ZeroOrthogonalPullback (coordinateRotationIsometry i j θ) v) =
    referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) u v := by
  have h := referenceTwoAngleFullWeakEnergyFamily_outer_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l θ φ p (u : BallH1) (v : BallH1)
  simpa only [referenceTwoAngleWeakDirichletEnergyFamily,referenceTwoAngleWeakEnergyFamily,
    referenceRotationWeakDirichletEnergyFamily,referenceRotationWeakEnergyFamily,
    ContinuousLinearMap.comp_apply,nativeH1ZeroDualRestrictionL_apply,
    Submodule.subtypeL_apply,nativeH1ZeroOrthogonalPullback_coe] using h

lemma referenceTwoAngleWeakDirichletEnergyFamily_isInvertible_of_original
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (referenceTwoAngleWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))).IsInvertible := by
  let e := coordinateRotationIsometry i j θ
  let A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)
  let F : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceTwoAngleWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))
  let T : BallH1Zero →L[ℝ] BallH1Zero := (nativeH1ZeroOrthogonalPullback e).toContinuousLinearMap
  let S : BallH1Zero →L[ℝ] BallH1Zero := (nativeH1ZeroOrthogonalPullback e.symm).toContinuousLinearMap
  have hT (z : BallH1Zero) : T z = nativeH1ZeroOrthogonalPullback e z := rfl
  have hS (z : BallH1Zero) : S z = nativeH1ZeroOrthogonalPullback e.symm z := rfl
  have hST (z : BallH1Zero) : S (T z) = z :=
    (hS (T z)).trans ((congrArg (nativeH1ZeroOrthogonalPullback e.symm) (hT z)).trans
      (nativeH1ZeroOrthogonalPullback_symm_apply e z))
  have hTS (z : BallH1Zero) : T (S z) = z := by
    have hInverse : nativeH1ZeroOrthogonalPullback e
        (nativeH1ZeroOrthogonalPullback e.symm z) = z := by
      simpa only [LinearIsometryEquiv.symm_symm] using
        nativeH1ZeroOrthogonalPullback_symm_apply e.symm z
    exact (hT (S z)).trans
      ((congrArg (nativeH1ZeroOrthogonalPullback e) (hS z)).trans hInverse)
  have hCov (u v : BallH1Zero) : F (T u) (T v) = A u v :=
    (congrArg₂ (fun x y : BallH1Zero => F x y) (hT u) (hT v)).trans
      (referenceTwoAngleWeakDirichletEnergyFamily_outer_covariance
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l θ φ p u v)
  have hInv : A.IsInvertible :=
    referenceRotationWeakDirichletEnergyFamily_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc k l φ p hOriginal
  exact isInvertible_nativeZero_of_bilinear_rotation_covariance A F T S hST hTS hCov hInv

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleFullWeakEnergyFamily_outer_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakDirichletEnergyFamily_outer_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakDirichletEnergyFamily_isInvertible_of_original
