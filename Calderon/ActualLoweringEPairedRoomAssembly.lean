import Calderon.ActualLoweringEPairedEndpointConclusion

/-! Complete variable-room assembly after separately checked exact geometry
and physical projections. Getter absent; original literal boundary retained. -/
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

local notation "EndpointFields" => LoweringEPairedEndpointFields
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EndpointConclusion" => LoweringEPairedEndpointConclusion
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Combine already chosen low-family facts with the named exact original
physical field projections. These are intermediate structural facts, not final
analytic callback premises. -/
theorem lowering_highRoom_paired_fields (δ0 d : ℝ)
    (P : LoweringEHighRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d)
    (Ll Rl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg)
    (hLowSm : ∀ i j, ContDiffOn ℝ ∞ (Ll i j) (ParamRoom d) ∧
      ContDiffOn ℝ ∞ (Rl i j) (ParamRoom d))
    (hLowFacts :
      (∀ i j t, t ∈ ParamRoom d →
        (Ll i j t).comp IH = (JL).comp (P.left i j t) ∧
        (Rl i j t).comp IH = (JL).comp (P.right i j t) ∧
        (I33).comp (Ll i j t) = (v016TransposeL (P.right i j t)).comp JL ∧
        (I33).comp (Rl i j t) = (v016TransposeL (P.left i j t)).comp JL ∧
        ‖Ll i j t‖ ≤ (‖P.left i j t‖ + ‖P.right i j t‖)/2 ∧
        ‖Rl i j t‖ ≤ (‖P.left i j t‖ + ‖P.right i j t‖)/2))
    (hCaps :
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ,
        n ≤ N → ∀ t ∈ ParamRoom d,
          ‖iteratedFDerivWithin ℝ n (P.left i j) (ParamRoom d) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (P.right i j) (ParamRoom d) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Ll i j) (ParamRoom d) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Rl i j) (ParamRoom d) t‖ ≤ M)
) :
    EndpointFields d P.left P.right Ll Rl := by
  refine ⟨?_, lowering_highRoom_exact_leftGraph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P,
    lowering_highRoom_exact_rightGraph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P,
    lowering_highRoom_exact_paired g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P,hLowFacts,hCaps⟩
  intro i j
  have hSm := lowering_highRoom_exact_smooth g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P i j
  exact ⟨hSm.1,hSm.2,(hLowSm i j).1,(hLowSm i j).2⟩

/-- Entire original endpoint conclusion on a variable original HighRoom,
using only the already checked geometry/projections and paired-low bridge. -/
theorem lowering_paired_endpointConclusion_of_high_room (δ0 d : ℝ)
    (P : LoweringEHighRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d) :
    EndpointConclusion δ0 := by
  obtain ⟨Ll,Rl,hLowSm,hLowFacts,hCaps⟩ := exists_paired_lows_of_high_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P
    (lowering_paramRoom_isCompact y0 ρ d)
    (lowering_highRoom_uniqueDiff g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P)
  exact lowering_paired_endpointConclusion_intro
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P.pos P.le0 P.lerho
    (lowering_highRoom_exact_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P)
    P.left P.right Ll Rl
    (lowering_highRoom_paired_fields g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P Ll Rl hLowSm hLowFacts hCaps)

/-- Literal original public existential boundary; statement byte-identical to
Assembly012, with only one application to the named-conclusion theorem. -/
theorem exists_retained_lowering_E_paired_endpoints_of_high_room
    (δ0 d : ℝ) (P : LoweringEHighRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ L R : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half,
    ∃ Ll Rl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg,
      (∀ i j, ContDiffOn ℝ ∞ (L i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (R i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (Ll i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (Rl i j) (ParamRoom δ)) ∧
      (∀ i j t, t ∈ ParamRoom δ → ∀ u : Hi,
        JL (L i j t u) = aL i (EH j t u) - EL j t (aH i u)) ∧
      (∀ i j t, t ∈ ParamRoom δ → ∀ u : Hi,
        JL (R i j t u) = BL j t (AH i u) - AL i (BH j t u)) ∧
      (∀ i j t, t ∈ ParamRoom δ → ∀ u v : Hi,
        PP (IH v) (JL (L i j t u)) = PP (IH u) (JL (R i j t v))) ∧
      (∀ i j t, t ∈ ParamRoom δ →
        (Ll i j t).comp IH = (JL).comp (L i j t) ∧
        (Rl i j t).comp IH = (JL).comp (R i j t) ∧
        (I33).comp (Ll i j t) = (v016TransposeL (R i j t)).comp JL ∧
        (I33).comp (Rl i j t) = (v016TransposeL (L i j t)).comp JL ∧
        ‖Ll i j t‖ ≤ (‖L i j t‖ + ‖R i j t‖)/2 ∧
        ‖Rl i j t‖ ≤ (‖L i j t‖ + ‖R i j t‖)/2) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ,
        n ≤ N → ∀ t ∈ ParamRoom δ,
          ‖iteratedFDerivWithin ℝ n (L i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (R i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Ll i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Rl i j) (ParamRoom δ) t‖ ≤ M)
 :=
  lowering_paired_endpointConclusion_of_high_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d P

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
