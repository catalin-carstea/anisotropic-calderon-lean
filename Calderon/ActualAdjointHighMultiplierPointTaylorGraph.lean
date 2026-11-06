import Calderon.SignedTaylorIncludedCommutatorTransport
import Calderon.ActualAdjointHighMultiplierRadialCertificates
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

local instance instCompleteSpaceActualAdjointHighMultiplierPointTaylorGraphHighCarrier : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance instCompleteSpaceActualAdjointHighMultiplierPointTaylorGraphHalfCarrier : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance instCompleteSpaceActualAdjointHighMultiplierPointTaylorGraphHighEnd : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance
local instance instCompleteSpaceActualAdjointHighMultiplierPointTaylorGraphHighHalf : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

lemma referenceAdjointHighMultiplier_signedTaylor_inclusion_of_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (hg : IsAdmissibleMetric g) (Q : SmoothCoefficientJets 3)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (r d lam Lam : ℝ) (hr : |r| < d)
    (hTube : ∀ t : ℝ, |t| < d →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,t)),z)) lam Lam ∧
      UnitBallSmallDriftData (fun z => a ((q,(y,t)),z))
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)) lam ∧
      (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      (q,(y,t)) ∈ referenceGaugeNormalHighInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc) :
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
      (secondTaylorRemainder (fun t : ℝ => referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,t))) r) =
    (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q) -
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)).comp
        (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) := by
  let A : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun t =>
    referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,t))
  let S : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun t =>
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| < d := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hMul : |θ*r| ≤ |r| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)
    exact hMul.trans_lt hr
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) :=
    contDiffAt_referenceAdjointHighMultiplier_radialSlice
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg Q q y (θ*r)
        (hTube (θ*r) (hScaled θ hθ)).2.2.2
  have hSS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ S (θ*r) :=
    contDiffAt_referenceAdjointHighRadial_radialSlice
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y (θ*r)
        (hTube (θ*r) (hScaled θ hθ)).2.2.1
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t => I.comp (A t)) =ᶠ[𝓝 (θ*r)]
        (fun t => (S t).comp MH-ML.comp (S t)) := by
    apply eventually_referenceAdjointHighMultiplier_radial_inclusion
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel hg Q
        q hq y hy (θ*r) d lam Lam (hScaled θ hθ)
    intro t ht
    have hAt := hTube t ht
    exact ⟨hAt.1,hAt.2.1,hAt.2.2.1⟩
  have hGeneric := secondTaylorRemainder_included_commutator
    (X := SphereSobolev (3/2 : ℝ)) (Y := SphereSobolev (1/2 : ℝ))
  exact hGeneric A S I MH ML r hAS hSS hEq

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHighMultiplier_signedTaylor_inclusion_of_room
