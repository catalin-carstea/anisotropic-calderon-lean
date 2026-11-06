import Calderon.ActualLoweringEPairedLowBridge

/-! Focused original-room geometry and exact physical field projection
diagnostic. It does not assert the full paired producer or identify a getter
cause. Routine Sol implementation after the previously archived separate
read-only Astra advice; no new advice/review/model call. -/
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

lemma lowering_paramRoom_isCompact (d : ℝ) : IsCompact (ParamRoom d) :=
  (isCompact_commonRoom y0 ρ d).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)

lemma lowering_highRoom_uniqueDiff (δ0 d : ℝ)
    (P : LoweringEHighRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d) :
    UniqueDiffOn ℝ (ParamRoom d) :=
  (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 P.pos).prod
    (uniqueDiffOn_convex (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)

lemma lowering_highRoom_exact_room (δ0 d : ℝ)
    (P : LoweringEHighRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d) :
    commonRoom y0 ρ d ⊆ Ω := P.room

lemma lowering_highRoom_exact_smooth (δ0 d : ℝ)
    (P : LoweringEHighRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d) :
    ∀ i j, ContDiffOn ℝ ∞ (P.left i j) (ParamRoom d) ∧
      ContDiffOn ℝ ∞ (P.right i j) (ParamRoom d) := P.smooth

lemma lowering_highRoom_exact_leftGraph (δ0 d : ℝ)
    (P : LoweringEHighRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d) :
    ∀ i j t, t ∈ ParamRoom d → ∀ u : Hi,
      JL (P.left i j t u) = aL i (EH j t u) - EL j t (aH i u) := P.leftGraph

lemma lowering_highRoom_exact_rightGraph (δ0 d : ℝ)
    (P : LoweringEHighRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d) :
    ∀ i j t, t ∈ ParamRoom d → ∀ u : Hi,
      JL (P.right i j t u) = BL j t (AH i u) - AL i (BH j t u) := P.rightGraph

lemma lowering_highRoom_exact_paired (δ0 d : ℝ)
    (P : LoweringEHighRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 d) :
    ∀ i j t, t ∈ ParamRoom d → ∀ u v : Hi,
      PP (IH v) (JL (P.left i j t u)) = PP (IH u) (JL (P.right i j t v)) := P.paired

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
