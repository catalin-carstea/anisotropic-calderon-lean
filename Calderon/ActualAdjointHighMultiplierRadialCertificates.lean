import Calderon.ActualAdjointHighMultiplierRadialSmoothSlice
import Calderon.ActualAdjointHighRadialSmoothSlice
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

local instance instCompleteSpaceActualAdjointHighMultiplierRadialCertificatesHighCarrier : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance instCompleteSpaceActualAdjointHighMultiplierRadialCertificatesHalfCarrier : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance instCompleteSpaceActualAdjointHighMultiplierRadialCertificatesHighEnd : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance
local instance instCompleteSpaceActualAdjointHighMultiplierRadialCertificatesHighHalf : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

lemma eventually_referenceAdjointHighMultiplier_radial_inclusion
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (hg : IsAdmissibleMetric g) (Q : SmoothCoefficientJets 3)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (r d lam Lam : ℝ) (hr : |r| < d)
    (hRoom : ∀ t : ℝ, |t| < d →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,t)),z)) lam Lam ∧
      UnitBallSmallDriftData (fun z => a ((q,(y,t)),z))
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)) lam ∧
      (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (fun t : ℝ => (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
      (referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,t)))) =ᶠ[𝓝 r]
    (fun t : ℝ => (referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q) -
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)).comp
        (referenceAdjointThreeHalfRadialFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t)))) := by
  have hOpen : IsOpen {t : ℝ | |t| < d} := isOpen_lt continuous_abs continuous_const
  filter_upwards [hOpen.mem_nhds hr] with t ht
  have hAt := hRoom t ht
  have hWeak := isInvertible_referenceWeakDirichletEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t)) lam hAt.2.1
  have hy2 : ‖y-y0‖ ≤ 2*ρ := by linarith [hData.1.2.1]
  apply ContinuousLinearMap.ext
  intro f
  exact referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily_inclusion
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
      Q q hq y hy2 t lam Lam hAt.1 hAt.2.1.1 hWeak hAt.2.2 f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eventually_referenceAdjointHighMultiplier_radial_inclusion
