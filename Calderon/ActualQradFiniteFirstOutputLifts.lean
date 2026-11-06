import Calderon.ActualFiniteHarmonicProductRadialRemainderGraph
import Calderon.ActualFiniteGaugeAdjointRemainderGraph
import Calderon.ActualHighRadialCommutatorGainCore
import Calderon.ActualAdjacentGainedSameRoom
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion
attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL harmonicSphereSubspace
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialAdjointSharpSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutator
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder

attribute [local instance] adjacentGainThreeHalfComplete adjacentGainHalfComplete adjacentGainNegativeHalfComplete adjacentGainHighHighComplete adjacentGainHighHalfComplete adjacentGainHalfHalfComplete adjacentGainHalfNegComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))))

local notation "Ihi" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "Jlo" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "GHr" => referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "KbH" => referenceRadialAdjointSharpSecondCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "KbL" => referenceRadialAdjointSharpSecondCommutator
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "NMH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NML" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NMN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "RAH" => referenceAdjointThreeHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "RAL" => referenceAdjointHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "BCL" => referenceSmoothMultiplierBoundaryCommutatorFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "BCA" => referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

include hg in
theorem exists_reference_commonRadius_finite_radial_coefficient_first_output_lifts
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
      ∀ (n : ℕ) (Q : Fin 3 → SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)),
      ∃ rLift lLift : Fin 3 → SphereSobolev (3/2 : ℝ),
        (∀ i : Fin 3, Ihi (rLift i) =
          (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r)
            (NMH (Q i) (sphereSobolevPartialSum (3/2 : ℝ) n f))) ∧
        (∀ i : Fin 3, Ihi (lLift i) = NML (smoothMultiplierLowerJets (Q i))
          (Sh q y r (sphereSobolevPartialSum (3/2 : ℝ) n f))) := by
  have productRoom := exists_reference_commonRadius_finiteProductHighSecondRemainder_graph
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel
  rcases productRoom with ⟨dP,hdP,hdPρ,hProduct⟩
  have gaugeRoom := exists_reference_commonRadius_finiteGaugeAdjointSecondRemainder_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0 hKernel
  rcases gaugeRoom with ⟨dG,hdG,_,G,hGauge⟩
  have physicalRoom := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases physicalRoom with ⟨lam,Lam,d0,_,hd0,_,hRoom0⟩
  refine ⟨min dP (min dG (d0/2)),lt_min hdP (lt_min hdG (half_pos hd0)),
    (min_le_left _ _).trans hdPρ,?_⟩
  intro q hq y hy r hr n Q f
  have hrP : |r| ≤ dP := hr.trans (min_le_left _ _)
  have hrG : |r| ≤ dG := hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr2 : |r| ≤ d0/2 := hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr0 : |r| < d0 := hr2.trans_lt (by linarith)
  have hyBall : y ∈ closedBall y0 ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| ≤ d0 := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)).trans hr0.le
  have hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    fun θ hθ => (hRoom0 (q,(y,θ*r)) ⟨hq,hyBall,abs_le.mp (hScaled θ hθ)⟩).2.2.1
  have hTube : ∀ s : ℝ, |s| < d0 →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,s)),z)) lam Lam ∧
      (∀ z ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,s)),z)‖ ≤ lam/4) ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,s))).IsInvertible ∧
      (q,(y,s)) ∈ referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc := by
    intro s hs
    have hz := hRoom0 (q,(y,s)) ⟨hq,hyBall,abs_le.mp hs.le⟩
    refine ⟨hz.1,hz.2.1.1,
      isInvertible_referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,s)) lam hz.2.1,?_⟩
    unfold referenceGaugeNormalHighInvertibleLocus
    exact hz.2.2.2.1
  let u := sphereSobolevPartialSum (3/2 : ℝ) n f
  let rLift : Fin 3 → SphereSobolev (3/2 : ℝ) := fun i =>
    referenceFiniteGaugeAdjointSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (Q i) q y r f
  let pLift : Fin 3 → SphereSobolev (3/2 : ℝ) := fun i =>
    referenceFiniteHarmonicProductHighSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (Q i) q y r f
  let lLift : Fin 3 → SphereSobolev (3/2 : ℝ) := fun i => pLift i-GHr (Q i) q y r u
  refine ⟨rLift,lLift,?_,?_⟩
  · intro i
    exact hGauge q hq y hy r hrG n (Q i) f
  · intro i
    have hP : Ihi (pLift i) = Sh q y r (NMH (Q i) u) := by
      simpa only [pLift,u,referenceSharpRadialTraceSecondRemainder] using
        (hProduct q hq y hy r hrP n (Q i) f)
    have hLower := referenceHighSmoothMultiplierSecondRemainder_lower_inclusion
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hKernel (Q i) q y r d0 lam Lam
        hr0 hSegment hTube
    have hGH : Ihi (GHr (Q i) q y r u) =
        (secondTaylorRemainder (fun s : ℝ => BCL (Q i) (q,(y,s))) r) (Ihi u) := by
      simpa only [referenceHighSmoothMultiplierSecondRemainder,
        referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder,ContinuousLinearMap.comp_apply] using
        (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A u) hLower)
    have hGu := referenceSmoothMultiplierSecondRemainder_upper_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel (Q i) q y r hSegment u
    have hEq : Ihi (lLift i) = Sh q y r (NMH (Q i) u) -
        (Sh q y r (NMH (Q i) u) - NML (smoothMultiplierLowerJets (Q i)) (Sh q y r u)) :=
      ((Ihi).map_sub _ _).trans (congrArg₂ (fun x z : SphereSobolev (1/2 : ℝ) => x-z)
        hP (hGH.trans hGu))
    exact hEq.trans (sub_sub_cancel _ _)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
