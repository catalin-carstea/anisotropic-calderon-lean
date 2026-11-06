import Calderon.ActualLoweringEHighGraphSmooth

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

local notation "LP" => loweringMultiplierHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RP" => raisingMultiplierHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LF" => loweringEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RF" => reverseERaisingHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  reverseEHigh reverseELow retainedGeneratorHigh retainedGeneratorHalf retainedJets
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
  sphereSobolevShiftedDegreeL loweringHigh loweringLow raisingHigh raisingLow
  loweringMultiplierHigh raisingMultiplierHalf loweringEHigh reverseERaisingHigh

/-- Original same-W ingredients, isolated from the high product and low assembly declarations. -/
structure LoweringEPrerequisiteRoom (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) where
  pos : 0 < δ
  le0 : δ ≤ δ0
  lerho : δ ≤ ρ
  room : commonRoom y0 ρ δ ⊆ Ω
  G : Fin 3 → Pphys → Half →L[ℝ] Half
  generatorSmooth : ∀ V : Generator, ∀ c : RetainedCoefficient,
    ContDiffOn ℝ ∞ (GH δ0 W V c) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (GL δ0 W V c) (ParamRoom δ)
  generatorGraph : ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
    (∀ u : Hi, IH (GH δ0 W V c t u) = generatorHigh V (NH (QW δ0 W c t) u) -
      NL (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorHigh V u)) ∧
    (∀ v : Half, JL (GL δ0 W V c t v) = generatorLow V
      (NL (smoothMultiplierLowerJets (QW δ0 W c t)) v) -
      NN (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorLow V v))
  radialSmooth : ∀ i : Fin 3,
    ContDiffOn ℝ ∞ (CaT hreg G i) (commonRoom y0 ρ δ) ∧
      ContDiffOn ℝ ∞ (CAS hreg i) (commonRoom y0 ρ δ)
  radialLowerGraph : ∀ i t, t ∈ commonRoom y0 ρ δ → ∀ u : Hi,
    JL (CaT hreg G i t u) = aL i (Th t u) - Tl t (aH i u)
  radialRaiseGraph : ∀ i t, t ∈ commonRoom y0 ρ δ → ∀ u : Hi,
    JL (CAS hreg i t u) = AL i (Sh t u) - Sl t (AH i u)

/-- Complete high outputs, with genuine pairing, before low endpoint construction. -/
structure LoweringEHighRoom (δ0 δ : ℝ) where
  pos : 0 < δ
  le0 : δ ≤ δ0
  lerho : δ ≤ ρ
  room : commonRoom y0 ρ δ ⊆ Ω
  left : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half
  right : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half
  smooth : ∀ i j, ContDiffOn ℝ ∞ (left i j) (ParamRoom δ) ∧
    ContDiffOn ℝ ∞ (right i j) (ParamRoom δ)
  leftGraph : ∀ i j t, t ∈ ParamRoom δ → ∀ u : Hi,
    JL (left i j t u) = aL i (EH j t u) - EL j t (aH i u)
  rightGraph : ∀ i j t, t ∈ ParamRoom δ → ∀ u : Hi,
    JL (right i j t u) = BL j t (AH i u) - AL i (BH j t u)
  paired : ∀ i j t, t ∈ ParamRoom δ → ∀ u v : Hi,
    PP (IH v) (JL (left i j t u)) = PP (IH u) (JL (right i j t v))

local notation "Prereq" => LoweringEPrerequisiteRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HighRoom" => LoweringEHighRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

theorem exists_retained_lowering_E_prerequisite_room
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, Nonempty (Prereq hreg δ0 W δ) := by
  obtain ⟨dU, hdU, _hdU0, _hdUρ, hUS, hUG, _hUC⟩ :=
    exists_commonRoom_retained_generator_multiplier_gains
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  obtain ⟨dA, hdA, hdAρ, hRoomA, G, _hGS, _hGG, hCaT, _hSharp, hCAS⟩ :=
    exists_reference_commonRadius_angularHigh_both_graph_caps
      hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel
  let δ := min δ0 (min dU dA)
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdU hdA)
  have hδ0le : δ ≤ δ0 := min_le_left _ _
  have hδU : δ ≤ dU := (min_le_right _ _).trans (min_le_left _ _)
  have hδA : δ ≤ dA := (min_le_right _ _).trans (min_le_right _ _)
  have hSubU : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ dU := commonRoom_mono y0 ρ hδU
  have hSubA : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ dA := commonRoom_mono y0 ρ hδA
  have hPSubU : ParamRoom δ ⊆ ParamRoom dU := fun t ht => ⟨hSubU ht.1, ht.2⟩
  refine ⟨δ, ⟨{
    pos := hδ
    le0 := hδ0le
    lerho := hδA.trans hdAρ
    room := hSubA.trans hRoomA
    G := G
    generatorSmooth := fun V c => ⟨((hUS V c).1).mono hPSubU, ((hUS V c).2).mono hPSubU⟩
    generatorGraph := fun V c t ht => hUG V c t (hPSubU ht)
    radialSmooth := fun i => ⟨((hCaT i).2.1).mono hSubA, ((hCAS i).2.1).mono hSubA⟩
    radialLowerGraph := fun i t ht => (hCaT i).1 t (hSubA ht)
    radialRaiseGraph := fun i t ht => (hCAS i).1 t (hSubA ht) }⟩⟩

noncomputable def LoweringEPrerequisiteRoom.toHighRoom
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (P : Prereq hreg δ0 W δ) : HighRoom δ0 δ := by
  have hSub0 : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0 := commonRoom_mono y0 ρ P.le0
  have hSeg (t : Tpar) (ht : t ∈ ParamRoom δ) :=
    segment_of_mem_commonRoom hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData P.room t.1 ht.1
  have hSmooth (i j : Fin 3) :
      ContDiffOn ℝ ∞ (LF hreg δ0 W P.G i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (RF hreg δ0 W i j) (ParamRoom δ) :=
    lowering_E_both_smooth
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W P.G δ hSub0 P.room P.generatorSmooth P.radialSmooth i j
  have hLG (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u : Hi) :
      JL (LF hreg δ0 W P.G i j t u) = aL i (EH j t u) - EL j t (aH i u) :=
    loweringEHigh_graph_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W P.G i j t ⟨hSub0 ht.1, ht.2⟩ (hSeg t ht)
      (P.radialLowerGraph i t.1 ht.1) (fun V c => (P.generatorGraph V c t ht).1) u
  have hRG (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u : Hi) :
      JL (RF hreg δ0 W i j t u) = eL j t (AH i u) - AL i (eH j t u) :=
    reverseERaisingHigh_graph_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W i j t ⟨hSub0 ht.1, ht.2⟩
      (P.radialRaiseGraph i t.1 ht.1) (fun V c => (P.generatorGraph V c t ht).2) u
  refine {
    pos := P.pos
    le0 := P.le0
    lerho := P.lerho
    room := P.room
    left := LF hreg δ0 W P.G
    right := RF hreg δ0 W
    smooth := hSmooth
    leftGraph := hLG
    rightGraph := ?_
    paired := ?_ }
  · intro i j t ht u
    simpa only [ActualHigherSAdjointLeadingCoordinate.reverseEHigh_eq_ordered,
      ActualHigherSAdjointLeadingCoordinate.reverseELow_eq_ordered] using hRG i j t ht u
  · intro i j t ht u v
    exact lowering_E_paired_adjunction_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W P.G i j t ⟨hSub0 ht.1, ht.2⟩ (hSeg t ht)
      (hLG i j t ht) (hRG i j t ht) u v

theorem exists_retained_lowering_E_high_room
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, Nonempty (HighRoom δ0 δ) := by
  obtain ⟨δ, ⟨P⟩⟩ := exists_retained_lowering_E_prerequisite_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  exact ⟨δ, ⟨LoweringEPrerequisiteRoom.toHighRoom
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ P⟩⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
