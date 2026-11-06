import Calderon.ActualHigherSZeroCoefficientExpansions
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
open ReferenceDensityBounds ActualHigherSZeroCoefficientJetBounds
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
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


attribute [local irreducible] zeroParameterFactor
  ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient

/-- Full ordered Q-contraction of the genuine native second rows. -/
theorem canonical_zero_contracted_second_rows (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (x : R3)
    (hf : ∀ j : Fin 3, DifferentiableAt ℝ (EH j) ((Tq δr Ar p q) x)) :
    let t := (Tq δr Ar p q) x
    let r := referenceRadius δr Ar p L x
    let HH : Fin 3 × Fin 3 → ℝ := fun mk =>
      hessianEntry mk (fderiv ℝ (fderiv ℝ (referenceRadius δr Ar p L)) x)
    r^2 • (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t •
      ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
        (PH δr Ar p q) (fun k => EL k t) x i j) =
      r • (r • (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t • ZR i j t)+
        (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t • ZL i j t))+
      ∑ mk : Fin 3 × Fin 3, (r^2*HH mk) • PSI g2 mk t := by
  intro t r HH
  let zz : Fin 3 → Fin 3 → (Hi →L[ℝ] Neg) := fun i j => QP g2 i j t •
    ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
      (PH δr Ar p q) (fun k => EL k t) x i j
  let rr : Fin 3 → Fin 3 → (Hi →L[ℝ] Neg) := fun i j => QP g2 i j t • ZR i j t
  let ll : Fin 3 → Fin 3 → (Hi →L[ℝ] Neg) := fun i j => QP g2 i j t • ZL i j t
  let DD : Fin 3 → Fin 3 → (Fin 3 × Fin 3) → (Hi →L[ℝ] Neg) := fun i j mk =>
    QP g2 i j t • ((XP i t) mk.1 • (JL).comp (fderiv ℝ (EH j) t (hessianTangent mk.2)))
  have hrw (i j : Fin 3) : r^2 • zz i j = r • (r•rr i j+ll i j)+
      ∑ mk : Fin 3 × Fin 3, (r^2*HH mk) • DD i j mk := by
    have h := second_zero_row_factorisation g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      δr Ar p hδr hAr q x i j (hf j)
    exact smul_factored_row (V := Hi →L[ℝ] Neg) (QP g2 i j t) r
      _ _ _ HH (fun mk => (XP i t) mk.1 • (JL).comp (fderiv ℝ (EH j) t (hessianTangent mk.2))) h
  have hsum := sum_factored_rows_two (V := Hi →L[ℝ] Neg) r zz rr ll HH DD hrw
  have hsum' : r^2 • (∑ i : Fin 3, ∑ j : Fin 3, zz i j) =
      r • (r•(∑ i : Fin 3, ∑ j : Fin 3, rr i j)+∑ i : Fin 3, ∑ j : Fin 3, ll i j)+
      ∑ mk : Fin 3 × Fin 3, (r^2*HH mk) • PSI g2 mk t := hsum
  dsimp only [zz, rr, ll] at hsum'
  exact hsum'
end Native
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
