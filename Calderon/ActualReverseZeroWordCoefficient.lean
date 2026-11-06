import Calderon.ActualHigherSReverseZeroLinearSplit
import Calderon.ActualHigherSReverseZeroWordIdentity
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
/-- An exact native equality substitution, before any physical parameter context. -/
private lemma native_source_to_word
    (J : Half →L[ℝ] Neg) (Source Literal Word : Hi →L[ℝ] Neg)
    (Linear : Hi →L[ℝ] Half)
    (hSource : Source=Literal+J.comp Linear) (hWord : Literal=Word) :
    Source=Word+J.comp Linear := by
  cases hWord
  exact hSource

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

local notation "WT2" => ActualHigherSQuadraticZeroWords.quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact pointwise source-to-word corollary, with the original source hypotheses. -/
theorem source_adjoint_zero_coefficient_eq_words (g2 : MatrixField) (dr Ar : ℝ)
    (p : ℕ) (q : ℝ) (x : R3) :
    CT g2 dr Ar p q x = WT2 g2 dr Ar p q x+(JL).comp (T1 g2 dr Ar p q x) := by
  exact native_source_to_word (JL)
    (CT g2 dr Ar p q x) (T2 g2 dr Ar p q x)
    (WT2 g2 dr Ar p q x) (T1 g2 dr Ar p q x)
    (source_adjoint_zero_coefficient_eq_literal
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x)
    (literalQuadraticZeroReverseNegative_eq_words
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
