import Calderon.ActualZeroWordCoefficientPair
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
  ConformalDepth PrincipalCommutator ActualHigherSLinearZero
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
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CT" => ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  sphereSobolevInclusionL sphereSobolevShiftedDegreeL referenceHighHorizontalAngularL
  referenceLowerHorizontalAngularL referenceMetricGramFrame referenceDensityPrincipalFrameCoefficient
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

local notation "WQ2" => ActualHigherSQuadraticZeroWords.quadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "WT2" => ActualHigherSQuadraticZeroWords.quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Complete actual profile constructor, before any endpoint-room data context.
The sole profile premise is the geometric guard proved by the original packet. -/
theorem exists_uniform_source_zero_coefficient_pair
    (hreg : FixedDirichletRegularity) (d0 : ℝ) (W : CoeffRoom d0)
    (d : ℝ) (Cm : CRoom hreg d0 W d)
    (hJac : ∀ z ∈ commonRoom y0 ρ d, Jac z)
    (g2 : MatrixField) (eta0 etaWord : ℝ)
    (hetaWord : 0 < etaWord) (hetaWord0 : etaWord ≤ eta0)
    (hGuard : SamePacketZeroWordProfileRoom g L y0 ρ d etaWord) :
    ∃ etaBound : ℝ, 0 < etaBound ∧ etaBound ≤ eta0 ∧ ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaBound →
    ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
    1 ≤ actualReferenceBeta g L q dr Ar p x →
    referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
    CZ g2 dr Ar p q x = WQ2 g2 dr Ar p q x+(JL).comp (Z1 g2 dr Ar p q x) ∧
    CT g2 dr Ar p q x = WT2 g2 dr Ar p q x+(JL).comp (T1 g2 dr Ar p q x) := by
  refine ⟨etaWord, hetaWord, hetaWord0, ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs
  exact source_zero_coefficient_pair_eq_words
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg d0 W d Cm hJac g2 dr Ar p hdr hAr q hq x
    (hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
