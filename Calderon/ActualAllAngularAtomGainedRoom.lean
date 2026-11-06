import Calderon.ActualAllAngularAtomRoomAssembly

/-! Literal original actual all-atom producer. The same high packet is selected
from the original hypotheses; a complete variable-packet theorem assembles it.
All original definitions/record retain their original global namespace. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomGainedRoom
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows
  ActualPiJacobiRadialGainedRows ActualRetainedGeneratorMultiplierGains
  ActualGeneratorEPairedGainedEndpoints ActualCanonicalGeneratorAngularGainedRows
  ActualCanonicalAngularGainedBracket NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
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

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GG" => fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  Room hreg data.Gcoord data.GN data.δ0 data.germs
local notation "PC" => pairedLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PD" => pairedRightHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RA" => raisingHigh hF hO hD
local notation "RL" => raisingLow hF hO hD
local notation "LA" => loweringHigh hF hO hD
local notation "LL" => loweringLow hF hO hD
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RR" => angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  reverseEHigh reverseELow sphereSobolevInclusionL generatorHigh generatorLow
  generatorSharpHigh generatorSharpLow raisingHigh raisingLow loweringHigh loweringLow
  angularAtomHigh angularAtomLow angularAtomReverseHigh angularAtomReverseLow
  allAtomGainHigh generatorRaisingGainHigh loweringGeneratorGainHigh v016TransposeL

noncomputable def retainedAllAngularAtomHighRoom (hKernel : UnitBallValueTraceKernel τ0) :
    Σ d : ℝ, AllAngularAtomHighRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d := by
  classical
  let hRoom := exists_same_packet_allAngularAtom_high_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  exact ⟨Classical.choose hRoom,Classical.choice (Classical.choose_spec hRoom)⟩

attribute [local irreducible] retainedAllAngularAtomHighRoom

theorem exists_same_packet_allAngularAtom_room (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ data.δ ∧ d ≤ data.δ0 ∧ d ≤ ρ ∧ commonRoom y0 ρ d ⊆ Ω ∧
      Nonempty (AllAngularAtomRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d)
 := by
  let packet := retainedAllAngularAtomHighRoom
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  exact exists_same_packet_allAngularAtom_room_of_high_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data packet.1 packet.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomGainedRoom
