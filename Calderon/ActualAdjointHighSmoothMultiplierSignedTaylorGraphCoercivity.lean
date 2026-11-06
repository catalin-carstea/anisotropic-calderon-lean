import Calderon.SignedTaylorIncludedCommutatorTransport
import Calderon.ActualAdjointHighMultiplierPointTaylorGraph
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

local instance coercivityOct28ActualAdjointHighSmoothMultiplierSignedTaylorGraphComplete1 : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance coercivityOct28ActualAdjointHighSmoothMultiplierSignedTaylorGraphComplete2 : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance coercivityOct28ActualAdjointHighSmoothMultiplierSignedTaylorGraphComplete3 : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance
local instance coercivityOct28ActualAdjointHighSmoothMultiplierSignedTaylorGraphComplete4 : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

theorem exists_reference_commonRadius_adjointHighSmoothMultiplierSecondRemainder_graph
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (hg : IsAdmissibleMetric g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ δ →
        ∀ (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)),
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
            ((secondTaylorRemainder (fun t : ℝ => referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,t))) r) f) =
          secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
              (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q f) -
          nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
            (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r f) := by

  obtain ⟨lam,Lam,d,_,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d/2,by positivity,(by linarith),?_⟩
  intro q hq y hy r hr Q f
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hAt (t : ℝ) (ht : |t| < d) := hRoom (q,(y,t)) ⟨hq,hyBall,abs_le.mp ht.le⟩
  have hrStrict : |r| < d := by linarith
  have hGraph := referenceAdjointHighMultiplier_signedTaylor_inclusion_of_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel hg Q
      q hq y hy r d lam Lam hrStrict (by
        intro t ht
        have hz := hAt t ht
        refine ⟨hz.1,hz.2.1,hz.2.2.1,?_⟩
        unfold referenceGaugeNormalHighInvertibleLocus
        exact hz.2.2.2.1)
  have hValue := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T f) hGraph
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply] using hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_adjointHighSmoothMultiplierSecondRemainder_graph
