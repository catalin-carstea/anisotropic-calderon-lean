import Calderon.ActualHighAdjointMovingBoundaryFamilyDefinition
import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.SignedOperatorTaylorRemainder

/-! Full upfront: raw-moving-adjoint-split-author-oct16-v001/EXPANSION.md.
Exact unchanged selected declarations from compiled-only a974 Raw7. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

local instance : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceRadialEndpointInvertibleLocus referenceHighAdjointCoordinateBoundaryFamily
  referenceHighAdjointJacobiBoundaryCorrection referenceHighAdjointMovingBoundaryAction
  referenceHighAdjointMovingBoundaryActionFamily
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientJets
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL

def referenceHighAdjointRadialSecondRemainder (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r

def referenceHighAdjointMovingActualJetFirstCorrection
    (q : ℝ) (y : R3) (r f : ℝ) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0).comp (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)) +
    (r*f) • (deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0)

def referenceHighAdjointMovingActualJetNormalizedCorrection
    (q : ℝ) (y : R3) (r f : ℝ) (i : Fin 3) (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)) +
  referenceHighAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv +
    (r*f) • referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r

lemma referenceAdjointThreeHalfRadialFamily_signed_actual_jet_taylor
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ) (hSegment : ∀ t ∈ uIcc (0 : ℝ) r, (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) =
      referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) +
      r • (deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0) + r^2 • referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r := by
  let A : ℝ → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    fun t => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  have hSmooth : ∀ t ∈ uIcc (0 : ℝ) r, ContDiffAt ℝ ∞ A t := by
    intro t ht
    have hJoint := (contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment t ht))
    exact hJoint.comp (f := fun t : ℝ => (q,(y,t))) t
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  exact signed_taylor_integral_remainder A r hSmooth


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointRadialSecondRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingActualJetFirstCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingActualJetNormalizedCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointThreeHalfRadialFamily_signed_actual_jet_taylor
