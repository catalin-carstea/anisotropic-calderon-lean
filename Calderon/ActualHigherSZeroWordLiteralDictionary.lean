import Calderon.ActualHigherSZeroWordUniformProfiles
import Calderon.ActualHigherSZeroWordProfileRoom
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift ActualHigherSZeroCoefficientFactorisation
  ConformalDepth PrincipalCommutator ActualHigherSLinearZero ActualHigherSQuadraticZeroWords
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualJacobiAngularGainedRows SmoothMetricFrame MovingFrameConnection FixedParameterProfilePullback
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "Q2" => literalQuadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T2" => literalQuadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Z1" => linearZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => linearAdjointZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WQ2" => quadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WT2" => quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CT" => ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  sphereSobolevInclusionL sphereSobolevShiftedDegreeL sphereSobolevRotationL
  referenceHighHorizontalAngularL referenceLowerHorizontalAngularL
  referenceMetricGramFrame referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint referenceRadiusHorizontalLogDerivative

attribute [local irreducible] ActualHigherSCoefficientExtraction.secondZeroRow
  ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow
  ActualHigherSCoefficientExtraction.profileHigh ActualHigherSCoefficientExtraction.profileLow
  ActualHigherSAdjointCoefficientExtraction.reverseProfileHigh
  ActualHigherSAdjointCoefficientExtraction.reverseProfileLow
  ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient

attribute [local irreducible] literalQuadraticZeroNegative literalQuadraticZeroReverseNegative
  linearZeroHigh linearAdjointZeroHigh

variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)

set_option diagnostics true in
/-- Complete original-data construction of the literal all-profile dictionary formula.
This declaration separates retained-room elimination from public-predicate conversion. -/
theorem exists_same_packet_zero_word_dictionary_literal (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
  ∃ etaWord : ℝ,0 < etaWord ∧ etaWord ≤ data.eta0 ∧ ∀ q ∈ Icc (0 : ℝ) 1,
  ∀ dr : ℝ,∀ hdr : 0 < dr,dr ≤ 1 → ∀ Ar : ℝ,∀ hAr : 0 < Ar,∀ p : ℕ,1 ≤ p →
  ∀ eta : ℝ,0 ≤ eta → eta ≤ etaWord → ∀ x ∈ closedBall y0 ρ,x ∈ ball y0 ρ →
  1 ≤ actualReferenceBeta g L q dr Ar p x →
  referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
  CZ g2 dr Ar p q x=WQ2 g2 dr Ar p q x+(JL).comp (Z1 g2 dr Ar p q x) ∧
  CT g2 dr Ar p q x=WT2 g2 dr Ar p q x+(JL).comp (T1 g2 dr Ar p q x) := by
  dbg_trace "A013 proof entry"
  dbg_trace "A013 before retained 11-witness obtain"
  obtain ⟨etaWord,hetaWord,hetaWord0,dA,hdA,hdA0,hdArho,Cm,hJac,hAdj,hGuard⟩ :=
    exists_same_packet_zero_word_profile_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel
  dbg_trace "A013 after retained 11-witness obtain"
  dbg_trace "A013 before exact uniform constructor"
  exact exists_uniform_source_zero_coefficient_pair
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs dA Cm hJac g2 data.eta0 etaWord hetaWord hetaWord0 hGuard
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
