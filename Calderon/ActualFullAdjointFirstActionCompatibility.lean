import Calderon.ActualFullAdjointFirstActions

/-! Full AUTHOR upfront: actual-Y-second-action-domain-author-oct16-v001/EXPANSION-v001.md.
Literal formal Y=-H+Cprimal-GammaTrace; genuine global IBP remains separate. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighMovingBoundaryActionFamily
  referenceLowerMovingBoundaryActionFamily referenceHighMovingBoundaryAction
  referenceLowerMovingBoundaryAction referenceHighFullAdjointFirstAction
  referenceLowerFullAdjointFirstAction referenceMetricGramFrame
  referenceFrameConnectionCoefficient sphereSobolevInclusionL

lemma referenceMovingBoundaryActionFamily_high_lower_compatibility
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighMovingBoundaryActionFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i) =
    (referenceLowerMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hHigh := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => J.comp T)
    (referenceHighMovingBoundaryActionFamily_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i hInv)
  have hLow := congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T.comp I)
    (referenceLowerMovingBoundaryActionFamily_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i hInv)
  exact hHigh.trans ((referenceMovingBoundaryAction_high_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R y i hInv hNormal hStrong hWeak).trans hLow.symm)

lemma referenceFullAdjointFirstAction_high_lower_compatibility
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (hu : DifferentiableAt ℝ u y) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i) =
    referenceLowerFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u x)) y i := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let delta := ∑ j : Fin 3, referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) j) j i
  have hHorizontal := referenceHorizontalAction_high_lower_compatibility g L q u y i hu
  have hMoving := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (u y))
    (referenceMovingBoundaryActionFamily_high_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        q R y i hInv hNormal hStrong hWeak)
  have hScalar : J (delta • I (u y)) = delta • J (I (u y)) := J.map_smul delta (I (u y))
  have hTotal := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
    (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => -x+z) hHorizontal hMoving) hScalar
  simpa only [referenceHighFullAdjointFirstAction,referenceLowerFullAdjointFirstAction,
    map_sub,map_add,map_neg,ContinuousLinearMap.comp_apply,I,J,delta] using hTotal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceMovingBoundaryActionFamily_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFullAdjointFirstAction_high_lower_compatibility
