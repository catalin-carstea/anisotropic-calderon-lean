import Calderon.ActualLowerMovingBoundaryFamily
import Calderon.ActualAdjointMovingBoundaryAction
import Calderon.ActualReferenceAdjointRadialEndpointFamilies

/-! Full upfront: day-oct13/actual-moving-boundary-family-author-oct15-v001/
EXPANSION-adjoint-families-split.md. Unchanged public roots, definitions and
statements; only receipt/module boundaries are decomposed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open NativeCoefficientBoundaryMultiplier

/-! Full upfront: day-oct13/actual-moving-boundary-family-author-oct15-v001/
EXPANSION-adjoint-families.md. Actual genuine adjoints; no chosen jet smoothness
assumption and no physical P assertion. -/

local instance : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

def sphereLowerDistributionalTransposeL :
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
  realHilbertOperatorAdjointL (SphereSobolev (1/2 : ℝ))

theorem sphereLowerDistributionalTransposeL_apply
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
    sphereLowerDistributionalTransposeL A = sphereLowerDistributionalTranspose A := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceJacobiBoundaryCoefficientJets
  referenceJacobiBoundaryThreeHalfCoefficientJets referenceHighAdjointCoordinateBoundaryFamily
  referenceLowerAdjointCoordinateBoundaryFamily nativeThreeHalfCoefficientMulL
  referenceLowerMovingBoundaryActionFamily referenceLowerMovingBoundaryAction
  referenceHighAdjointJacobiBoundaryCorrection referenceHighAdjointMovingBoundaryAction

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem contDiffAt_referenceHighAdjointCoordinateBoundaryFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun t => referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t i) p := by
  have hRad :=
    (contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)
  unfold referenceHighAdjointCoordinateBoundaryFamily
  exact contDiffAt_const.add (hRad.clm_comp contDiffAt_const)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTransposeL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTransposeL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighAdjointCoordinateBoundaryFamily
