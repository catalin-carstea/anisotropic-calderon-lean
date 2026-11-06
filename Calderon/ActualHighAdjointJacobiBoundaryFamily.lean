import Calderon.ActualAdjointMovingBoundaryFamilyFoundation
import Calderon.ActualJacobiThreeHalfBoundaryMultiplierFamily

/-! Full upfront: day-oct13/actual-moving-boundary-family-author-oct15-v001/
EXPANSION-high-adjoint-family-split-v002.md. Unchanged six high-family public
roots and proofs; only Jacobi/moving receipt boundaries are decomposed. -/
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

def referenceHighAdjointJacobiBoundaryCorrectionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ j : Fin 3, (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j).comp
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j p))

theorem referenceHighAdjointJacobiBoundaryCorrectionFamily_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i =
    referenceHighAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 i hInv := by
  unfold referenceHighAdjointJacobiBoundaryCorrectionFamily referenceHighAdjointJacobiBoundaryCorrection
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun F : SmoothCoefficientJets 3 =>
    (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F))
    (referenceJacobiBoundaryThreeHalfCoefficientFamily_eq g hg L y0 Φ B ε C ρ H a w hData i j p hInv)

theorem contDiffAt_referenceHighAdjointJacobiBoundaryCorrectionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible)
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun t => referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t i) p := by
  apply ContDiffAt.sum
  intro j hj
  exact (contDiffAt_referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p j hp).clm_comp
    (contDiffAt_nativeThreeHalf_referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hInv)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointJacobiBoundaryCorrectionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointJacobiBoundaryCorrectionFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighAdjointJacobiBoundaryCorrectionFamily
