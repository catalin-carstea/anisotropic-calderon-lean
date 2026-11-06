import Calderon.ActualQradSectionContinuityAndHighGraph
import Calderon.ActualFinitePairedRadialRemainderClosedSections
import Calderon.ActualPiNativeOperatorGerms
import Calderon.ActualQradReferenceProfileEnergy
import Calderon.ActualFinitePairedRadialRemainderSections
import Calderon.ActualFinitePhysicalWeakSquaredNorm
import Calderon.ActualQradJointCoefficientCaps
import Calderon.ActualQradFiniteFirstOutputLifts
import Calderon.ActualHighSmoothMultiplierSecondRadialRemainderTopologyCoercivity

/-! Original-Pi Qrad self row as a difference of two SEPARATELY integrable weighted squared norms
(author-only successor, v010). Complete expansion: output/MATHEMATICS.md (N0–N7), written before
these declarations. Imports the proposed parent `Calderon.ActualOriginalPiQradReferenceProfile`
without redoing it. No compiler was run; no acceptance is claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion
open ActualFiniteHarmonicCore ActualFiniteHarmonicModel ReferenceDensityBounds ConformalDepth
  ReferenceWeightedApproximation

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL harmonicSphereSubspace
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  referenceRadialAdjointSharpSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutator
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow
  commonSupportCoefficientFamily referencePiThreeHalfMultiplier referencePiHalfMultiplier
  referencePiNegativeHalfMultiplier referenceDensityPrincipalFrameCoefficient finiteCoreSobolevLift
  referenceFiniteHarmonicProductHighSecondRemainder referenceFiniteGaugeAdjointSecondRemainder

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
local notation "Z0" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "GHr" => referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "BCL" => referenceSmoothMultiplierBoundaryCommutatorFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "NMH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NML" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NMN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "RAH" => referenceAdjointThreeHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "RAL" => referenceAdjointHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "CH" => referenceAdjacentGainedCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "CL" => referenceAdjacentGainedCommutatorLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "PiH" => referencePiThreeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-! ### N3 (L1): continuity patch — continuous on a closed set, input vanishing off it. -/

attribute [local irreducible] sphereSobolevPartialSum qradSignedWeakSelfExpression qradFourIndexWeakForm

theorem continuous_compact_referenceQrad_output
    (K : Set R3) (hK : IsCompact K) (R : R3 → ℝ) (hR : Continuous R)
    (Q : R3 → Fin 3 → Fin 3 → ℝ) (hQ : ∀ i j, Continuous (fun y => Q y i j))
    (Bop : Fin 3 → Fin 3 → R3 → Hi →L[ℝ] Half)
    (v : Fin 3 → Fin 3 → R3 → Hi)
    (hB : ∀ i j y, y ∈ K → ContinuousAt (Bop i j) y)
    (hv : ∀ i j, Continuous (v i j))
    (hz : ∀ i j y, y ∉ K → v i j y=0) :
    let O : R3 → SphereSobolev (0 : ℝ) := fun y =>
      R y^3 • ∑ i, ∑ j, Q y i j • Z0 (Bop i j y (v i j y))
    Continuous O ∧ HasCompactSupport O ∧ ∀ y, y ∉ K → O y=0 := by
  intro O
  have hV : ∀ i j, Continuous (fun y => Bop i j y (v i j y)) :=
    fun i j => continuous_clm_apply_of_closed_vanishing K hK.isClosed (Bop i j) (v i j)
      (hv i j) (hB i j) (hz i j)
  have hO : Continuous O :=
    (hR.pow 3).smul (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (hQ i j).smul ((Z0).continuous.comp (hV i j)))
  have hZero : ∀ y, y ∉ K → O y=0 := by
    intro y hy
    simp only [O,hz _ _ y hy,map_zero,smul_zero,Finset.sum_const_zero]
  exact ⟨hO,HasCompactSupport.intro hK hZero,hZero⟩

lemma referenceQrad_output_congr
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (v w : Fin 3 → Fin 3 → Half)
    (h : ∀ i j, v i j = w i j) :
    r^3 • ∑ i, ∑ j, Q i j • Z0 (v i j) =
      r^3 • ∑ i, ∑ j, Q i j • Z0 (w i j) := by
  simp only [h]

theorem weighted_norm_difference_integrable_of_continuous_compact
    (mu : R3 → ℝ) (hmu : Continuous mu)
    (O Aout : R3 → SphereSobolev (0 : ℝ))
    (hOc : Continuous O) (hAc : Continuous Aout)
    (hOcpt : HasCompactSupport O) (hAcpt : HasCompactSupport Aout)
    (W : R3 → ℝ) (hW : ∀ y, W y = ‖O y‖^2 - ‖Aout y‖^2) :
    Integrable (fun y => mu y * ‖O y‖^2) ∧
    Integrable (fun y => mu y * ‖Aout y‖^2) ∧
    (∫ y : R3, mu y * W y) = (∫ y : R3, mu y * ‖O y‖^2) - ∫ y : R3, mu y * ‖Aout y‖^2 := by
  have hIO : Integrable (fun y => mu y * ‖O y‖^2) :=
    integrable_weighted_norm_sq_of_continuous_compact _ hmu O hOc hOcpt
  have hIA : Integrable (fun y => mu y * ‖Aout y‖^2) :=
    integrable_weighted_norm_sq_of_continuous_compact _ hmu Aout hAc hAcpt
  have hFun : (fun y => mu y * W y) = (fun y => mu y * ‖O y‖^2 - mu y * ‖Aout y‖^2) :=
    funext fun y => (congrArg (fun t : ℝ => mu y*t) (hW y)).trans (mul_sub _ _ _)
  exact ⟨hIO,hIA,(congrArg (fun f : R3 → ℝ => ∫ y : R3, f y) hFun).trans (integral_sub hIO hIA)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
