import Calderon.ActualHigherSQuadraticZeroQuartic
import Calderon.ActualHigherSQuarticBound
import Calderon.ActualHigherSLinearZeroScalarCaps
import Calderon.ActualLowerSSelfFormation
import Calderon.ActualHigherSIntegratedPairing
import Calderon.FixedParameterProfilePullback
import Calderon.ActualHigherSPairingNormDiagnostic

/-! Complete actual207-word quartic uniform estimate, author source UNCOMPILED.
Own conditional source interfaces are not native/provider grants. Scalar cap
producer758c6aa5 was consumed ONLY through its exact declaration and upfront,
under Root's explicit conditional-interface grant; no new proof body was read.
No analytic callback escapes the final theorem. Original source/body/API/owner/
norm/literature-relative37 holds and pending human ratification remain. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
  ActualHigherSQuadraticZeroQuartic ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds ReferenceWeightedApproximation FixedParameterProfilePullback
  ActualScalarPrincipalAdjoint SpectralWeightedGraph SectionFiveErrorForms SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GG" => fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  Room hreg data.Gcoord data.GN data.δ0 data.germs
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "RD" => ActualCommonFirstWordQuadraticAdjoint.revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "WC" => actualWordCoefficient g L

local notation "VA" => actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "QR" => quarticWordRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

local notation "RAH" => ActualAllAngularAtomGainedRoom.angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RRH" => ActualAllAngularAtomGainedRoom.angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RAL" => ActualAllAngularAtomGainedRoom.angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact original row bound with the explicitly selected SAME standard pairing norm. -/
lemma exists_quarticWordRow_uniform_bound {d : ℝ} (P : ARoom d) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t ∈ ParamRoom d, ∀ U : Hi, ∀ z v : ZeroWord,
      |QR P t U z v| ≤
        4*ActualHigherSPairingNormDiagnostic.standardPairingNorm PL*M^3*‖U‖^2 := by
  obtain ⟨M, hM, hAtoms, hGains⟩ := P.finiteCaps 0
  refine ⟨M, hM, ?_⟩
  intro t ht U z v
  have hRoomA (b : ZeroAtom) : ‖RAH t b‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).1
  have hRoomB (b : ZeroAtom) : ‖RRH t b‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).2.2.1
  have hRoomAL (b : ZeroAtom) : ‖RAL t b‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).2.1
  have hA (b : ZeroAtom) : ‖AH t b‖ ≤ M :=
    (congrArg (fun K : Hi →L[ℝ] Half => ‖K‖)
      (ActualHigherSZeroAtomDictionary.atomHigh_eq_angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)).le.trans (hRoomA b)
  have hB (b : ZeroAtom) : ‖RH t b‖ ≤ M :=
    (congrArg (fun K : Hi →L[ℝ] Half => ‖K‖)
      (ActualHigherSZeroAtomDictionary.atomReverseHigh_eq_angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)).le.trans (hRoomB b)
  have hAL (b : ZeroAtom) : ‖AL t b‖ ≤ M :=
    (congrArg (fun K : Half →L[ℝ] Neg => ‖K‖)
      (ActualHigherSZeroAtomDictionary.atomLow_eq_angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)).le.trans (hRoomAL b)
  have hG (b e : ZeroAtom) : ‖P.gainHigh b e t‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hGains b e 0 le_rfl t ht).1
  have hCl (b e : ZeroAtom) : ‖P.gainLow b e t‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hGains b e 0 le_rfl t ht).2
  have h := ActualHigherSPairingNormDiagnostic.abs_four_native_pairings_le
    (AH t) (RH t) (fun b e => P.gainHigh b e t) (AL t) (fun b e => P.gainLow b e t)
    M (zero_le_one.trans hM) hA hB hG hAL hCl U
    (wordAtoms z).1 (wordAtoms z).2 (wordAtoms v).1 (wordAtoms v).2
  simpa only [quarticWordRow, ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
