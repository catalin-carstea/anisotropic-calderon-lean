import Calderon.ActualHighAdjointMovingBoundaryFamily
import Calderon.ActualMovingBoundaryTransposeIdentification

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceJacobiBoundaryCoefficientJets
  referenceJacobiBoundaryThreeHalfCoefficientJets referenceHighAdjointCoordinateBoundaryFamily
  referenceLowerAdjointCoordinateBoundaryFamily nativeThreeHalfCoefficientMulL
  referenceJacobiBoundaryThreeHalfCoefficientFamily
  referenceLowerMovingBoundaryActionFamily referenceLowerMovingBoundaryAction
  referenceHighAdjointJacobiBoundaryCorrection referenceHighAdjointMovingBoundaryAction

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hg : IsAdmissibleMetric g)

def referenceLowerAdjointMovingBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  sphereLowerDistributionalTransposeL
    (referenceLowerMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R t i)

theorem referenceLowerAdjointMovingBoundaryActionFamily_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,((t.2,R t.2),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (t.1,(t.2,R t.2))).IsInvertible) :
    referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R t i =
    referenceLowerAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t.1 R t.2 i hInv := by
  exact (sphereLowerDistributionalTransposeL_apply _).trans
    ((congrArg sphereLowerDistributionalTranspose
      (referenceLowerMovingBoundaryActionFamily_eq g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R t i hInv)).trans
        (sphereLowerDistributionalTranspose_referenceLowerMovingBoundary
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t.1 R t.2 i hInv hWeak))

theorem contDiffAt_referenceLowerAdjointMovingBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R t.2) (hr : R t.2 ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,((t.2,R t.2),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (t.1,(t.2,R t.2))).IsInvertible) :
    ContDiffAt ℝ ∞ (fun s => referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R s i) t := by
  have hLow := contDiffAt_referenceLowerMovingBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R t i hR hr hInv hNormal hWeak
  exact sphereLowerDistributionalTransposeL.contDiff.contDiffAt.comp t hLow

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointMovingBoundaryActionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointMovingBoundaryActionFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceLowerAdjointMovingBoundaryActionFamily
