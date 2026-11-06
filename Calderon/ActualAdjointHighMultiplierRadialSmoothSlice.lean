import Calderon.SignedTaylorIncludedCommutatorTransport
import Calderon.ActualHighAdjointSmoothMultiplierBoundaryGraph
import Calderon.ActualReferenceAdjointRadialEndpointConstruction
import Calderon.SequenceLpNaturalStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.SignedTaylorFixedLinearTransport

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceAdjointThreeHalfRadialFamily nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL sphereSobolevInclusionL
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  referenceRadialEndpointInvertibleLocus referenceGaugeNormalHighInvertibleLocus secondTaylorRemainder

local instance instCompleteSpaceActualAdjointHighMultiplierRadialSmoothSliceHighCarrier : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance instCompleteSpaceActualAdjointHighMultiplierRadialSmoothSliceHalfCarrier : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance instCompleteSpaceActualAdjointHighMultiplierRadialSmoothSliceHighEnd : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance
local instance instCompleteSpaceActualAdjointHighMultiplierRadialSmoothSliceHighHalf : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

lemma contDiffAt_referenceAdjointHighMultiplier_radialSlice
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hg : IsAdmissibleMetric g) (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) (r : ℝ)
    (hp : (q,(y,r)) ∈ referenceGaugeNormalHighInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc) :
    ContDiffAt ℝ ∞ (fun t : ℝ => referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,t))) r := by
  exact (contDiffAt_referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,r)) hp).comp
      (f := fun t : ℝ => (q,(y,t))) r
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceAdjointHighMultiplier_radialSlice
