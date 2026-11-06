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

/-- Open radial germ of the included high commutator on the extended `2ρ` centre range:
the existing high graph is applied directly at every point of the open radial room. -/
lemma eventually_referenceAdjointHighMultiplier_radial_inclusion_of_extended_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (hg : IsAdmissibleMetric g) (Q : SmoothCoefficientJets 3)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
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
  apply ContinuousLinearMap.ext
  intro f
  exact referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily_inclusion
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
      Q q hq y hy t lam Lam hAt.1 hAt.2.1.1 hWeak hAt.2.2 f

/-- DIAGNOSTIC TRIM D3 (full target intentionally absent): C^∞ of both radial slices at every
`θ*r`, `θ ∈ [0,1]`, from the true tube. -/
lemma contDiffAt_referenceAdjointHigh_radialSlices_of_extended_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hg : IsAdmissibleMetric g) (Q : SmoothCoefficientJets 3)
    (q : ℝ) (y : R3) (r d lam Lam : ℝ) (hr : |r| < d)
    (hTube : ∀ t : ℝ, |t| < d →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,t)),z)) lam Lam ∧
      UnitBallSmallDriftData (fun z => a ((q,(y,t)),z))
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)) lam ∧
      (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      (q,(y,t)) ∈ referenceGaugeNormalHighInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc) :
    (∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ (fun t : ℝ =>
      referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,t))) (θ*r)) ∧
    (∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ (fun t : ℝ =>
      referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (θ*r)) := by
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| < d := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hMul : |θ*r| ≤ |r| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)
    exact hMul.trans_lt hr
  exact ⟨fun θ hθ => contDiffAt_referenceAdjointHighMultiplier_radialSlice
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg Q q y (θ*r)
        (hTube (θ*r) (hScaled θ hθ)).2.2.2,
    fun θ hθ => contDiffAt_referenceAdjointHighRadial_radialSlice
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y (θ*r)
        (hTube (θ*r) (hScaled θ hθ)).2.2.1⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
