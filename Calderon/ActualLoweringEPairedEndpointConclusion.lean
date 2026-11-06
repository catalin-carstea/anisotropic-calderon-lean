import Calderon.ActualLoweringEHighRoomFacts

/-! Literal original endpoint conclusion, with a separate fixed-family tuple
constructor. No new endpoint assumptions are exported by the final producer. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualCanonicalAngularGainedBracket ActualCanonicalGeneratorAngularGainedRows
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

attribute [local irreducible] sphereSobolevInclusionL v016TransposeL

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GH" => retainedGeneratorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GL" => retainedGeneratorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sh" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sl" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "CH" => gainedAtOrder hF hO hD (3/2 : ℝ)
local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j (1 : ℝ))
local notation "CaT" => loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CAS" => raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  reverseEHigh reverseELow retainedGeneratorHigh retainedGeneratorHalf retainedJets
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL sphereSobolevShiftedDegreeL
  loweringHigh loweringLow raisingHigh raisingLow loweringMultiplierHigh raisingMultiplierHalf
  loweringEHigh reverseERaisingHigh referenceRadialEndpointInvertibleLocus

/-- The exact conjunction of endpoint fields in the original public target. -/
def LoweringEPairedEndpointFields (δ : ℝ)
    (Lf Rf : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half)
    (Ll Rl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg) : Prop :=
      (∀ i j, ContDiffOn ℝ ∞ (Lf i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (Rf i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (Ll i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (Rl i j) (ParamRoom δ)) ∧
      (∀ i j t, t ∈ ParamRoom δ → ∀ u : Hi,
        JL (Lf i j t u) = aL i (EH j t u) - EL j t (aH i u)) ∧
      (∀ i j t, t ∈ ParamRoom δ → ∀ u : Hi,
        JL (Rf i j t u) = BL j t (AH i u) - AL i (BH j t u)) ∧
      (∀ i j t, t ∈ ParamRoom δ → ∀ u v : Hi,
        PP (IH v) (JL (Lf i j t u)) = PP (IH u) (JL (Rf i j t v))) ∧
      (∀ i j t, t ∈ ParamRoom δ →
        (Ll i j t).comp IH = (JL).comp (Lf i j t) ∧
        (Rl i j t).comp IH = (JL).comp (Rf i j t) ∧
        (I33).comp (Ll i j t) = (v016TransposeL (Rf i j t)).comp JL ∧
        (I33).comp (Rl i j t) = (v016TransposeL (Lf i j t)).comp JL ∧
        ‖Ll i j t‖ ≤ (‖Lf i j t‖ + ‖Rf i j t‖)/2 ∧
        ‖Rl i j t‖ ≤ (‖Lf i j t‖ + ‖Rf i j t‖)/2) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ,
        n ≤ N → ∀ t ∈ ParamRoom δ,
          ‖iteratedFDerivWithin ℝ n (Lf i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Rf i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Ll i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Rl i j) (ParamRoom δ) t‖ ≤ M)


local notation "EndpointFields" => LoweringEPairedEndpointFields
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Literal original existential, factoring only its final conjunction. -/
def LoweringEPairedEndpointConclusion (δ0 : ℝ) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ Lf Rf : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half,
    ∃ Ll Rl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg,
      EndpointFields δ Lf Rf Ll Rl

local notation "EndpointConclusion" => LoweringEPairedEndpointConclusion
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Typed existential introduction on fixed families, independently of any
high-room record, choice/accessor, low construction or geometric proof. -/
theorem lowering_paired_endpointConclusion_intro
    (δ0 d : ℝ) (hd : 0 < d) (hd0 : d ≤ δ0) (hdρ : d ≤ ρ)
    (hRoom : commonRoom y0 ρ d ⊆ Ω)
    (Lf Rf : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half)
    (Ll Rl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg)
    (hFields : EndpointFields d Lf Rf Ll Rl) : EndpointConclusion δ0 :=
  ⟨d,hd,hd0,hdρ,hRoom,Lf,Rf,Ll,Rl,hFields⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
