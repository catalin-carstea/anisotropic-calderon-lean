import Calderon.ActualHigherSZeroRowFactorisation
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


/-- Literal constructor substitution, isolated before finite contraction and analytic jet estimates. -/
lemma canonical_zero_constructor_at_profile (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    let t := (Tq δr Ar p q) x
    let r := referenceRadius δr Ar p L x
    CZc g2 δr Ar p q x =
      (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t •
        ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
          (PH δr Ar p q) (fun k => EL k t) x i j)+
        r^2 • (∑ i : Fin 3, DP g2 i t • (JL).comp (EH i t)))+
      r • (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t •
        ((sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i).comp (EH j t)+
          (EL i t).comp (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j)))+
      r^3 • (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t • (EL i t).comp (EH j t)) := by
  intro t r
  let Z := ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
    (PH δr Ar p q) (fun k => EL k t) x
  let E0 : Fin 3 → Hi →L[ℝ] Half := fun j => PH δr Ar p q j x
  let E1 : Fin 3 → Hi →L[ℝ] Half := fun j => EH j t
  let low : Fin 3 → Half →L[ℝ] Neg := fun j => EL j t
  let A0 := sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ)
  let A1 := sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)
  have hE : E0 = E1 := by
    funext j
    change PH δr Ar p q j x = EH j t
    unfold ActualHigherSCoefficientExtraction.profileHigh
    rfl
  have he := congrArg (fun E : Fin 3 → Hi →L[ℝ] Half =>
    ActualHigherSCoefficientExtraction.zeroCoefficient r (fun i j => QP g2 i j t)
      (fun i => DP g2 i t) Z E low A0 A1) hE
  have hstart : CZc g2 δr Ar p q x =
      ActualHigherSCoefficientExtraction.zeroCoefficient r (fun i j => QP g2 i j t)
        (fun i => DP g2 i t) Z E0 low A0 A1 := by
    unfold ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      ActualHigherSZeroCoefficientJets.zeroCoefficientWith
    rfl
  have hexp := zeroCoefficient_expansion r (fun i j => QP g2 i j t)
    (fun i => DP g2 i t) Z E1 low A0 A1
  exact hstart.trans (he.trans hexp)

/-- Definitional non-Hessian factor expansion at the actual profile, without any room agreement argument. -/
lemma zero_parameter_factor_at_profile (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    let t := (Tq δr Ar p q) x
    let r := referenceRadius δr Ar p L x
    PHI g2 t = r • (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t • ZR i j t)+
      (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t • ZL i j t)+
      r • (∑ i : Fin 3, DP g2 i t • (JL).comp (EH i t))+
      (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t •
        ((sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i).comp (EH j t)+
          (EL i t).comp (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j)))+
      r^2 • (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t • (EL i t).comp (EH j t)) := by
  intro t r
  unfold zeroParameterFactor
  rfl

end Native
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
