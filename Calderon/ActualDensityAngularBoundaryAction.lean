import Calderon.ActualMovingBoundaryTransposeIdentification
import Calderon.ActualNormalizedSecondMetricDrift

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalizedPrincipalMetric ReferenceDensityBounds
  ActualNormalizedSecondMetricDrift ActualHorizontalNormBridge

/-! Both angular factors are actual genuine adjoints. This is not the full physical P. -/

attribute [local irreducible] referenceJacobiBoundaryCoefficientJets
  referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceHighAdjointMovingBoundaryAction referenceLowerAdjointMovingBoundaryAction
  referenceLowerMovingBoundaryAction

def referenceDensityPrincipalFrameCoefficient
    (g g2 : MatrixField) (L q : ℝ) (y : R3) (i j : Fin 3) : ℝ :=
  ∑ k : Fin 3, ∑ l : Fin 3,
    referenceNormalizedPrincipalMatrix g g2 L q y k l *
      referenceCoFrameEntry g L k i (q,y) * referenceCoFrameEntry g L l j (q,y)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceDensityDoubleAdjointAngularAction
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i j : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  (referenceLowerAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv).comp
    (referenceHighAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j hInv)

theorem referenceDensityDoubleAdjointAngularAction_eq_transpose_comp
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i j : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    referenceDensityDoubleAdjointAngularAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i j hInv =
    (sphereLowerDistributionalTranspose
      (referenceLowerMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv)).comp
        (referenceHighAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j hInv) := by
  rw [sphereLowerDistributionalTranspose_referenceLowerMovingBoundary
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv hWeak]
  rfl

theorem sphereSobolevDualPairing_referenceDensityDoubleAdjointAngularAction
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i j : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (u : SphereSobolev (3/2 : ℝ)) (v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (referenceDensityDoubleAdjointAngularAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i j hInv u) =
    sphereSobolevDualPairing (1/2 : ℝ)
      (referenceHighAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j hInv u)
      (referenceLowerMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv v) :=
  (sphereSobolevDualPairing_referenceLowerMovingBoundary_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv hWeak v
      (referenceHighAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j hInv u)).symm

def referenceDensityPureAngularBoundaryAction
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ) (y : R3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  R y • ((∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      referenceDensityDoubleAdjointAngularAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i j hInv) +
    ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceHighAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv))

theorem sphereSobolevDualPairing_referenceDensityPureAngularBoundaryAction
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ) (y : R3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hreg : FixedDirichletRegularity)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (u : SphereSobolev (3/2 : ℝ)) (v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (referenceDensityPureAngularBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y hInv u) =
    R y * ((∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j *
        sphereSobolevDualPairing (1/2 : ℝ)
          (referenceHighAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j hInv u)
          (referenceLowerMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv v)) +
      ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) *
        sphereSobolevDualPairing (1/2 : ℝ)
          (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)
          (referenceLowerMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv v)) := by
  have hAngular (i j : Fin 3) :=
    sphereSobolevDualPairing_referenceDensityDoubleAdjointAngularAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i j hInv hWeak u v
  have hDrift (i : Fin 3) :
      sphereSobolevDualPairing (1/2 : ℝ) v
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referenceHighAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv u)) =
      sphereSobolevDualPairing (1/2 : ℝ)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)
        (referenceLowerMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv v) := by
    have hCompat := congrArg
      (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A u)
      (referenceAdjointMovingBoundaryAction_high_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i hInv hWeak)
    exact (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      sphereSobolevDualPairing (1/2 : ℝ) v z) hCompat).trans
        (sphereSobolevDualPairing_referenceLowerMovingBoundary_adjoint
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv hWeak v
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)).symm
  change ⟪v,referenceDensityPureAngularBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y hInv u⟫_ℝ = _
  simp only [referenceDensityPureAngularBoundaryAction,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    real_inner_smul_right,inner_add_right,inner_sum]
  apply congrArg (fun z : ℝ => R y * z)
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun z : ℝ => referenceDensityPrincipalFrameCoefficient g g2 L q y i j * z)
      (hAngular i j)
  · apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun z : ℝ => normalizedSecondDriftFrameJoint g g2 L i (q,y) * z) (hDrift i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityPrincipalFrameCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityDoubleAdjointAngularAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityDoubleAdjointAngularAction_eq_transpose_comp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceDensityDoubleAdjointAngularAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityPureAngularBoundaryAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceDensityPureAngularBoundaryAction
