import Calderon.ActualMixedHorizontalSobolevPairing
import Calderon.ActualCovariantDensityFirstActions
import Calderon.ActualMovingBoundaryTransposeIdentification
import Calderon.ActualHighMovingBoundaryAction

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
DENSITY-FIRST-PAIRING-DEFECT-EXPANSION-v001.md. Actual product rule retains its exact trace defect. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic SmoothMetricFrame MovingFrameConnection ConnectionError

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

attribute [local irreducible] referenceHighMovingBoundaryAction referenceLowerMovingBoundaryAction
  referenceLowerAdjointMovingBoundaryAction referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceHighHorizontalAction referenceLowerHorizontalAction referenceMetricGramFrame
  referenceLowerAdjointMovingBoundaryActionFamily sphereSobolevInclusionL sphereSobolevDualPairing

theorem sphereSobolevDualPairing_referenceHighMovingBoundary_mixed_adjoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (v : SphereSobolev (1/2 : ℝ)) (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          q R y i hInv u)) =
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (referenceLowerAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        q R y i hInv v)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hCompatibility := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A u)
    (referenceMovingBoundaryAction_high_lower_compatibility g L y0 Φ B ε C ρ H a w hData hg
      hcalc hF hO hD τ0 q R y i hInv hNormal hStrong hWeak)
  have hTransport := congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) => sphereSobolevDualPairing (1/2 : ℝ) v z) hCompatibility
  have hAdjoint := sphereSobolevDualPairing_referenceLowerMovingBoundary_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv hWeak (I u) v
  have hSymmetry : sphereSobolevDualPairing (1/2 : ℝ) (I u)
      (referenceLowerAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        q R y i hInv v) =
      sphereSobolevDualPairing (-(1/2 : ℝ))
        (referenceLowerAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          q R y i hInv v) (I u) := by
    simp only [sphereSobolevDualPairing]
    exact real_inner_comm _ _
  exact hTransport.trans (hAdjoint.trans hSymmetry)

theorem fderiv_referenceLowerDensityValuePairing_defect
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (v : R3 → SphereSobolev (1/2 : ℝ)) (u : R3 → SphereSobolev (3/2 : ℝ))
    (hv : DifferentiableAt ℝ v y) (hu : DifferentiableAt ℝ u y) :
    fderiv ℝ (fun x => sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (v x))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u x))) y
      (referenceMetricGramFrame g L (q,y) i) =
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y)) +
    sphereSobolevDualPairing (1/2 : ℝ) (v y)
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighHorizontalAction g L q u y i -
          referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            q R y i hInv (u y))) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let A := referenceLowerAdjointMovingBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
  let C0 := referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    q R y i hInv
  have hProduct := fderiv_referenceMixedHorizontalValuePairing g L q v u y i hv hu
  have hAdjoint := sphereSobolevDualPairing_referenceHighMovingBoundary_mixed_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv hNormal hStrong hWeak (v y) (u y)
  have hFamily := congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (v y))
    (referenceLowerAdjointMovingBoundaryActionFamily_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i hInv hWeak)
  have hAdjointFamily : ⟪v y,J (C0 (u y))⟫_ℝ = ⟪A (v y),I (u y)⟫_ℝ := by
    have hScalar := hAdjoint.trans (congrArg
      (fun z : SphereSobolev (-(1/2 : ℝ)) => sphereSobolevDualPairing (-(1/2 : ℝ)) z (I (u y)))
      hFamily.symm)
    simpa only [sphereSobolevDualPairing] using hScalar
  rw [hProduct]
  simp only [referenceLowerDensityFirstAction, sphereSobolevDualPairing,
    map_sub, inner_sub_right, inner_add_left]
  change ⟪referenceLowerHorizontalAction g L q v y i,I (u y)⟫_ℝ +
      ⟪v y,J (referenceHighHorizontalAction g L q u y i)⟫_ℝ =
    (⟪referenceLowerHorizontalAction g L q v y i,I (u y)⟫_ℝ + ⟪A (v y),I (u y)⟫_ℝ) +
      (⟪v y,J (referenceHighHorizontalAction g L q u y i)⟫_ℝ - ⟪v y,J (C0 (u y))⟫_ℝ)
  have hScalarAlgebra (x y z t : ℝ) (ht : t=z) :
      x+y = (x+z)+(y-t) := by linarith
  exact hScalarAlgebra _ _ _ _ hAdjointFamily

theorem fderiv_referenceHighDensityValuePairing_defect
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (v u : R3 → SphereSobolev (3/2 : ℝ))
    (hv : DifferentiableAt ℝ v y) (hu : DifferentiableAt ℝ u y) :
    fderiv ℝ (fun x => sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (v x)))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u x))) y
      (referenceMetricGramFrame g L (q,y) i) =
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y)) +
    sphereSobolevDualPairing (1/2 : ℝ)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (v y))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighHorizontalAction g L q u y i -
          referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            q R y i hInv (u y))) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hvI := I.hasFDerivAt.comp y hv.hasFDerivAt
  have hProduct := fderiv_referenceLowerDensityValuePairing_defect
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv hNormal hStrong hWeak
      (fun z => I (v z)) u hvI.differentiableAt hu
  have hCompatible := referenceDensityFirstAction_high_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i hInv hWeak v hv
  have hTransport := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
    sphereSobolevDualPairing (-(1/2 : ℝ)) z (I (u y)) +
      sphereSobolevDualPairing (1/2 : ℝ) (I (v y))
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referenceHighHorizontalAction g L q u y i -
            referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
              q R y i hInv (u y)))) hCompatible
  exact hProduct.trans hTransport.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceHighMovingBoundary_mixed_adjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.fderiv_referenceLowerDensityValuePairing_defect
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.fderiv_referenceHighDensityValuePairing_defect
