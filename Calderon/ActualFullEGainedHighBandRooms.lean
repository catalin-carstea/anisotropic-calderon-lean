import Calderon.ActualFullEComplementarySmooth

/-! Source-only Sol author candidate. Full upfront: full-finite-assembly-before-v001.
All maps below use the actual retained coefficient germs. This file assembles the
literal full E/E HIGH graph, smooth paired LOW endpoint, and finite joint
jet caps. The new
ordinary reverse adapters are a declared unqualified dependency; no analytic
callback is added. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

@[instance_reducible] private def fullHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] fullHighNormed
@[instance_reducible] private def fullHighSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] fullHighSpace
@[instance_reducible] private def fullLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] fullLowNormed
@[instance_reducible] private def fullLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] fullLowSpace
@[instance_reducible] private def fullNegativeNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] fullNegativeNormed
@[instance_reducible] private def fullNegativeSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] fullNegativeSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rh" => originalRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rl" => originalRadialLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sh" => originalRadialReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sl" => originalRadialReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hh" => jacobiAngularOperatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hl" => jacobiAngularOperatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hh" => jacobiAngularReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hl" => jacobiAngularReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RR" => retainedAdjacentHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "RH" => radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HR" => angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HH" => jacobiAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  originalRadialHigh originalRadialLow
  originalRadialReverseHigh originalRadialReverseLow jacobiAngularOperatorHigh jacobiAngularOperatorLow
  jacobiAngularReverseHigh jacobiAngularReverseLow zeroCorrectionHigh zeroCorrectionHalf
  zeroReverseHigh zeroReverseHalf sphereSobolevInclusionL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL

attribute [local irreducible] fullGainedHigh retainedAdjacentHigh radialAngularHigh angularRadialHigh
  jacobiAngularHigh commonRoom referenceRadialEndpointInvertibleLocus

theorem hhHigh_smooth_graph_room
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ δ0 ∧ d ≤ ρ ∧
      (∀ i j : Fin 3, ContDiffOn ℝ ∞ (HH δ0 W i j) (commonRoom y0 ρ d)) ∧
      (∀ i j : Fin 3, ∀ p ∈ commonRoom y0 ρ d, ∀ u : Hi,
        JL (HH δ0 W i j p u)=hl i p (Hh j p u)-Hl j p (hh i p u)) := by
  classical
  let witnesses := exists_commonRoom_jacobiAngular_gained_rows
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  let d : ℝ := Classical.choose witnesses
  have hd := Classical.choose_spec witnesses
  have hf := Classical.choose_spec hd.2.2.2
  exact ⟨d,hd.1,hd.2.1,hd.2.2.1,fun i j => (hf.1 i j).1,hf.2.1⟩

theorem rrHigh_smooth_graph_room
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ δ0 ∧ d ≤ ρ ∧
      (∀ i j : Fin 3, ContDiffOn ℝ ∞ (RR δ0 W i j) (ParamRoom d)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom d, ∀ u : Hi,
        JL (RR δ0 W i j t u)=sl i t (Rh j t u)-Rl j t (sh i t u)) := by
  classical
  let witnesses := exists_commonRoom_retained_actualPi_adjacent_rows
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel δ0 hδ0 W
  let d : ℝ := Classical.choose witnesses
  have hd := Classical.choose_spec witnesses
  exact ⟨d,hd.1,hd.2.1,hd.2.2.1,fun i j => (hd.2.2.2.1 i j).1,
    fun i j t ht u => (hd.2.2.2.2.1 i j t ht u).2⟩


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
