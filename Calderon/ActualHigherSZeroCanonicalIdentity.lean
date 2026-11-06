import Calderon.ActualHigherSZeroContractedRows
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
open ReferenceDensityBounds ActualHigherSZeroCoefficientJetBounds
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
section ModuleAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
/-- Pure real-linear assembly; the algebra requires no norm instance. -/
lemma factorisation_from_three_expansions (r : ℝ)
    (C P A B D H Q S Z : V)
    (hC : C = (r^2•Z+r^2•D)+r•Q+r^3•S)
    (hZ : r^2•Z = r•(r•A+B)+H)
    (hP : P = r•A+B+r•D+Q+r^2•S) : C = r•P+H := by
  rw [hC,hP,hZ]
  module
end ModuleAlgebra

open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ConformalDepth ReferenceWeightedApproximation ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualGeneratorRadialGainedRows ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms SphereHarmonic.DegreeGraphLifting ActualHorizontalNormBridge NormalCoordinatesFrame
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def factorHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorHighNormed
@[instance_reducible] private def factorHighSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorHighSpace
@[instance_reducible] private def factorLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] factorLowNormed
@[instance_reducible] private def factorLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] factorLowSpace
@[instance_reducible] private def factorZeroNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] factorZeroNormed
@[instance_reducible] private def factorZeroSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] factorZeroSpace
@[instance_reducible] private def factorParameterNormed : NormedAddCommGroup Tpar := inferInstance
attribute [local instance] factorParameterNormed
@[instance_reducible] private def factorParameterSpace : NormedSpace ℝ Tpar := inferInstance
attribute [local instance] factorParameterSpace
@[instance_reducible] private def factorDerivativeNormed : NormedAddCommGroup (Tpar →L[ℝ] Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorDerivativeNormed
@[instance_reducible] private def factorDerivativeSpace : NormedSpace ℝ (Tpar →L[ℝ] Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorDerivativeSpace

attribute [local irreducible] ActualHigherSCoefficientExtraction.zeroCoefficient
attribute [local irreducible] canonicalHigh canonicalLow referenceDensityPrincipalFrameCoefficient
 normalizedSecondDriftFrameJoint referenceMetricGramFrame

section Native
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "XP" => parameterGramFrame g L
local notation "GP" => parameterConnection g L
local notation "OL" => parameterLowerAngular g L
local notation "OH" => parameterHighAngular g L
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QP" g2:max i:max j:max t:max => referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 i j
local notation "DP" g2:max i:max t:max => normalizedSecondDriftFrameJoint g g2 L i (t.1.1,t.1.2.1)

local notation "ZR" => regularZeroRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => logarithmicZeroRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PHI" => zeroParameterFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PSI" => zeroHessianFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PH" => ActualHigherSCoefficientExtraction.profileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
attribute [local irreducible] ActualHigherSCoefficientExtraction.secondZeroRow
 ActualHigherSCoefficientExtraction.profileHigh regularZeroRow logarithmicZeroRow parameterGramFrame


attribute [local irreducible] zeroParameterFactor zeroHessianFactor
  ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient

theorem canonical_zero_factor_identity (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (x : R3)
    (hf : ∀ j : Fin 3, DifferentiableAt ℝ (EH j) ((Tq δr Ar p q) x)) :
    CZc g2 δr Ar p q x = referenceRadius δr Ar p L x • PHI g2 ((Tq δr Ar p q) x)+
      ∑ mk : Fin 3 × Fin 3, ((referenceRadius δr Ar p L x)^2 •
        hessianEntry mk (fderiv ℝ (fderiv ℝ (referenceRadius δr Ar p L)) x)) •
        PSI g2 mk ((Tq δr Ar p q) x)  := by
  have hNative := canonical_zero_constructor_at_profile g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 g2 δr Ar p q x
  have hRows := canonical_zero_contracted_second_rows g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 g2 δr Ar p hδr hAr q x hf
  have hPhi := zero_parameter_factor_at_profile g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 g2 δr Ar p q x
  apply ContinuousLinearMap.ext
  intro v
  have hc := congrArg (fun A : Hi →L[ℝ] Neg => A v) hNative
  have hz := congrArg (fun A : Hi →L[ℝ] Neg => A v) hRows
  have hp := congrArg (fun A : Hi →L[ℝ] Neg => A v) hPhi
  exact @factorisation_from_three_expansions Neg _ _ (referenceRadius δr Ar p L x)
    _ _ _ _ _ _ _ _ _ hc hz hp

end Native
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
