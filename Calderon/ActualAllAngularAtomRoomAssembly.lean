import Calderon.ActualAllAngularAtomHighRoom
import Calderon.ActualAllAngularAtomFiniteCaps

/-! Complete actual room assembly on a variable original high packet. All low
facts and finite caps are derived, with no analytic cap callback or new final
premise. Original public definitions/record are imported from their high owner. -/
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

private lemma low_eq_of_comp_inclusion_eq (C D : Half →L[ℝ] Neg)
    (h : C.comp IH = D.comp IH) : C = D := by
  apply ContinuousLinearMap.ext
  intro v
  refine (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).induction_on v
    (isClosed_eq C.continuous D.continuous) ?_
  intro U
  simpa only [ContinuousLinearMap.comp_apply] using congrArg (fun A : Hi →L[ℝ] Neg => A U) h

local notation "HighRoom" => AllAngularAtomHighRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "AtomRoom" => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

lemma allAngularAtom_paramRoom_isCompact (d : ℝ) : IsCompact (ParamRoom d) :=
  (isCompact_commonRoom y0 ρ d).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)

lemma allAngularAtom_highRoom_uniqueDiff (d : ℝ) (P : HighRoom d) :
    UniqueDiffOn ℝ (ParamRoom d) :=
  (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 P.pos).prod
    (uniqueDiffOn_convex (convex_closedBall _ _)
      ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)

/-- Complete final original record on a variable original high packet. -/
theorem exists_allAngularAtom_room_of_high_room (d : ℝ) (P : HighRoom d) :
    Nonempty (AtomRoom d) := by
  have hPD : ParamRoom d ⊆ ParamRoom data.δ := fun t ht =>
    ⟨commonRoom_mono y0 ρ P.leData ht.1,ht.2⟩
  have hK := allAngularAtom_paramRoom_isCompact y0 ρ d
  have hUnique := allAngularAtom_highRoom_uniqueDiff
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d P
  obtain ⟨Cl,hCl,_hNativeMidpoint,_hGainedCaps⟩ :=
    ActualAllAngularAtomPairedLow.exists_finite_paired_low_family (ι := AngularAtom)
      (ParamRoom d) hK hUnique P.gainHigh P.gainSmooth P.paired
  have hRetainedLow (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom d) :
      Cl (Sum.inl i) (Sum.inl j) t = data.Cl i j t := by
    apply low_eq_of_comp_inclusion_eq
    calc
      _ = (JL).comp (P.gainHigh (Sum.inl i) (Sum.inl j) t) := ((hCl _ _).2 t ht).1
      _ = (JL).comp (GG i j t) := by rw [P.retainedEEHigh i j t ht]
      _ = _ := ((data.low_graph i j t (hPD ht)).1).symm
  have hCaps := ActualAllAngularAtomFiniteCaps.exists_allN_atom_and_gain_caps
    (ι := AngularAtom) (ParamRoom d) hK hUnique AH RH AL RR P.gainHigh Cl
    P.atomSmooth P.gainSmooth (fun a b => (hCl a b).1)
  exact ⟨{
    gainHigh := P.gainHigh
    gainLow := Cl
    atomSmooth := P.atomSmooth
    gainSmooth := fun a b => ⟨P.gainSmooth a b,(hCl a b).1⟩
    atomGraph := P.atomGraph
    reverseAtomGraph := P.reverseAtomGraph
    atomPivot := P.atomPivot
    gainGraph := P.gainGraph
    upper := fun a b t ht => ((hCl a b).2 t ht).1
    lower := fun a b t ht => ((hCl a b).2 t ht).2.1
    paired := P.paired
    midpoint := fun a b t ht => ((hCl a b).2 t ht).2.2
    retainedEEHigh := P.retainedEEHigh
    retainedEELow := hRetainedLow
    finiteCaps := hCaps }⟩

/-- Entire literal original geometry/existence conclusion from a variable
packet. Geometric, graph and cap premises are all discharged internally. -/
theorem exists_same_packet_allAngularAtom_room_of_high_room
    (d : ℝ) (P : HighRoom d) :
    ∃ d : ℝ, 0 < d ∧ d ≤ data.δ ∧ d ≤ data.δ0 ∧ d ≤ ρ ∧ commonRoom y0 ρ d ⊆ Ω ∧
      Nonempty (AllAngularAtomRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d)
 :=
  ⟨d,P.pos,P.leData,P.le0,P.lerho,P.room,
    exists_allAngularAtom_room_of_high_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d P⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomGainedRoom
