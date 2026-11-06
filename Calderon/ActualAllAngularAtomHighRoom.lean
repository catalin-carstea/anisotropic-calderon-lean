import Calderon.ActualLeadingPhysicalSignedSecondForm
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualCanonicalGeneratorAngularGainedRows
import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.ActualLoweringEPairedEndpoints
import Calderon.ActualFixedGeneratorPairedGains
import Calderon.ActualAllAngularAtomPairedLow
import Calderon.ActualAllAngularAtomNativeBudgets

/-! Complete actual high-room prerequisite. Original public atom definitions,
nine-case gained dictionary and final AllAngularAtomRoom record are retained
byte-identically in their original namespace. Complete low/finite-cap assembly
is separated and is not asserted by this high prerequisite alone. All source,
owner, norm, native and review qualifications remain; no acceptance claimed. -/
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

abbrev AngularAtom := (Fin 3) ⊕ (Generator ⊕ Fin 3)

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

def angularAtomHigh (t : Tpar) : AngularAtom → Hi →L[ℝ] Half
  | Sum.inl i => EH i t
  | Sum.inr (Sum.inl V) => generatorHigh V
  | Sum.inr (Sum.inr i) => RA i
def angularAtomLow (t : Tpar) : AngularAtom → Half →L[ℝ] Neg
  | Sum.inl i => EL i t
  | Sum.inr (Sum.inl V) => generatorLow V
  | Sum.inr (Sum.inr i) => RL i
def angularAtomReverseHigh (t : Tpar) : AngularAtom → Hi →L[ℝ] Half
  | Sum.inl i => BH i t
  | Sum.inr (Sum.inl V) => generatorSharpHigh V
  | Sum.inr (Sum.inr i) => LA i
def angularAtomReverseLow (t : Tpar) : AngularAtom → Half →L[ℝ] Neg
  | Sum.inl i => BL i t
  | Sum.inr (Sum.inl V) => generatorSharpLow V
  | Sum.inr (Sum.inr i) => LL i
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RR" => angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def generatorRaisingGainHigh (V : Generator) (j : Fin 3) : Hi →L[ℝ] Half :=
  match V with
  | Sum.inl ab => -rotationRaisingHigh hF hO hD ab.1 ab.2 j
  | Sum.inr _ => RA j
def loweringGeneratorGainHigh (i : Fin 3) (V : Generator) : Hi →L[ℝ] Half :=
  match V with
  | Sum.inl ab => -rotationLoweringHigh hF hO hD ab.1 ab.2 i
  | Sum.inr _ => LA i

def allAtomGainHigh
    (lowerLeft lowerRight : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half)
    (a b : AngularAtom) (t : Tpar) : Hi →L[ℝ] Half :=
  match a, b with
  | Sum.inl i, Sum.inl j => GG i j t
  | Sum.inr (Sum.inl V), Sum.inl j => PC hreg data.δ0 data.germs V j t
  | Sum.inl i, Sum.inr (Sum.inl V) => PD hreg data.δ0 data.germs V i t
  | Sum.inr (Sum.inr i), Sum.inl j => lowerLeft i j t
  | Sum.inl i, Sum.inr (Sum.inr j) => lowerRight j i t
  | Sum.inr (Sum.inl V), Sum.inr (Sum.inl W) =>
      ActualFixedGeneratorPairedGains.fixedGeneratorGainHigh V W
  | Sum.inr (Sum.inl V), Sum.inr (Sum.inr j) => generatorRaisingGainHigh hF hO hD V j
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inl V) => loweringGeneratorGainHigh hF hO hD i V
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => gainedAtOrder hF hO hD (3/2 : ℝ) i j
local notation "CG" => allAtomGainHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

structure AllAngularAtomRoom (d : ℝ) where
  gainHigh : AngularAtom → AngularAtom → Tpar → Hi →L[ℝ] Half
  gainLow : AngularAtom → AngularAtom → Tpar → Half →L[ℝ] Neg
  atomSmooth : ∀ a : AngularAtom,
    ContDiffOn ℝ ∞ (fun t => AH t a) (ParamRoom d) ∧
    ContDiffOn ℝ ∞ (fun t => AL t a) (ParamRoom d) ∧
    ContDiffOn ℝ ∞ (fun t => RH t a) (ParamRoom d) ∧
    ContDiffOn ℝ ∞ (fun t => RR t a) (ParamRoom d)
  gainSmooth : ∀ a b : AngularAtom,
    ContDiffOn ℝ ∞ (gainHigh a b) (ParamRoom d) ∧
    ContDiffOn ℝ ∞ (gainLow a b) (ParamRoom d)
  atomGraph : ∀ a t, t ∈ ParamRoom d → ∀ U : Hi, JL (AH t a U) = AL t a (IH U)
  reverseAtomGraph : ∀ a t, t ∈ ParamRoom d → ∀ U : Hi, JL (RH t a U) = RR t a (IH U)
  atomPivot : ∀ a t, t ∈ ParamRoom d → ∀ v z : Half, PP v (AL t a z) = PP z (RR t a v)
  gainGraph : ∀ a b t, t ∈ ParamRoom d → ∀ U : Hi,
    JL (gainHigh a b t U) = RR t a (AH t b U) - AL t b (RH t a U)
  upper : ∀ a b t, t ∈ ParamRoom d → (gainLow a b t).comp IH = (JL).comp (gainHigh a b t)
  lower : ∀ a b t, t ∈ ParamRoom d →
    (I33).comp (gainLow a b t) = (v016TransposeL (gainHigh b a t)).comp JL
  paired : ∀ a b t, t ∈ ParamRoom d → ∀ U V : Hi,
    PP (IH V) (JL (gainHigh a b t U)) = PP (IH U) (JL (gainHigh b a t V))
  midpoint : ∀ a b t, t ∈ ParamRoom d →
    ‖gainLow a b t‖ ≤ (‖gainHigh a b t‖ + ‖gainHigh b a t‖)/2
  retainedEEHigh : ∀ i j t, t ∈ ParamRoom d → gainHigh (Sum.inl i) (Sum.inl j) t = GG i j t
  retainedEELow : ∀ i j t, t ∈ ParamRoom d → gainLow (Sum.inl i) (Sum.inl j) t = data.Cl i j t
  finiteCaps : ∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧
    (∀ a : AngularAtom, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom d,
      ‖iteratedFDerivWithin ℝ n (fun s => AH s a) (ParamRoom d) t‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (fun s => AL s a) (ParamRoom d) t‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (fun s => RH s a) (ParamRoom d) t‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (fun s => RR s a) (ParamRoom d) t‖ ≤ M) ∧
    (∀ a b : AngularAtom, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom d,
      ‖iteratedFDerivWithin ℝ n (gainHigh a b) (ParamRoom d) t‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (gainLow a b) (ParamRoom d) t‖ ≤ M)


attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  reverseEHigh reverseELow sphereSobolevInclusionL generatorHigh generatorLow
  generatorSharpHigh generatorSharpLow raisingHigh raisingLow loweringHigh loweringLow
  angularAtomHigh angularAtomLow angularAtomReverseHigh angularAtomReverseLow
  allAtomGainHigh generatorRaisingGainHigh loweringGeneratorGainHigh v016TransposeL

private lemma generator_compat (V : Generator) (U : Hi) :
    JL (generatorHigh V U) = generatorLow V (IH U) := by
  cases V with
  | inl ij =>
    simpa only [generatorHigh, generatorLow, ContinuousLinearMap.comp_apply] using congrArg (fun A : Hi →L[ℝ] Neg => A U)
      (sphereSobolevRotationL_threehalf_half_compatibility ij.1 ij.2)
  | inr z =>
    simpa only [generatorHigh, generatorLow, ContinuousLinearMap.comp_apply] using
      congrArg (fun A : Hi →L[ℝ] Neg => A U) sphereSobolevShiftedDegree_high_half_compatibility

private lemma generatorSharp_compat (V : Generator) (U : Hi) :
    JL (generatorSharpHigh V U) = generatorSharpLow V (IH U) := by
  cases V with
  | inl ij => simpa only [generatorSharpHigh, generatorSharpLow, ContinuousLinearMap.neg_apply, map_neg] using
      congrArg (fun n : Neg => -n) (generator_compat (Sum.inl ij) U)
  | inr z => simpa only [generatorSharpHigh, generatorSharpLow] using generator_compat (Sum.inr z) U

private lemma generator_low_pivot (V : Generator) (x y : Half) :
    PP x (generatorLow V y) = PP y (generatorSharpLow V x) := by
  cases V with
  | inl ij =>
    have h := sphereSobolevDualPairing_half_rotation_skew ij.1 ij.2 y x
    have h0 : PP x (sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 y) =
        -PP y (sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 x) :=
      (real_inner_comm x (sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 y)).symm.trans h
    simpa only [generatorLow, generatorSharpLow, ContinuousLinearMap.neg_apply,
      sphereSobolevDualPairing, inner_neg_right] using h0
  | inr z =>
    have h := sphereSobolevDualPairing_lower_distributionalTranspose
      (sphereSobolevShiftedDegreeL (1/2 : ℝ)) y x
    rw [sphereLowerDistributionalTranspose_shiftedDegree_half] at h
    simpa only [generatorLow, generatorSharpLow] using h

private theorem atom_facts_at (t : Tpar) (ht : t ∈ ParamRoom data.δ) :
    (∀ a U, JL (AH t a U) = AL t a (IH U)) ∧
    (∀ a U, JL (RH t a U) = RR t a (IH U)) ∧
    (∀ a (v z : Half), PP v (AL t a z) = PP z (RR t a v)) := by
  have ht0 : t ∈ ParamRoom data.δ0 := ⟨commonRoom_mono y0 ρ data.δ_le0 ht.1, ht.2⟩
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData data.parameter_subset t.1 ht.1
  have hE (i : Fin 3) (U : Hi) : JL (EH i t U) = EL i t (IH U) := by
    have hp := (data.germs.piGerm i t ht0).self_of_nhds
    exact canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg i t hSeg (ActualPiJacobiRadialGainedRows.piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        data.δ0 data.germs i t) hp.1 hp.2.1 U
  have hB (i : Fin 3) (U : Hi) : JL (BH i t U) = BL i t (IH U) := by
    have hp := (data.germs.piGerm i t ht0).self_of_nhds
    simpa only [orderedReverseHigh, orderedReverseLow, originalRadialReverseHigh,
      originalRadialReverseLow, jacobiAngularReverseHigh, jacobiAngularReverseLow] using
      explicit_ordered_reverse_high_low_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t hSeg
        (ActualPiJacobiRadialGainedRows.piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          data.δ0 data.germs i t) hp.2.1 hp.2.2 U
  have hP (i : Fin 3) (v z : Half) : PP v (EL i t z) = PP z (BL i t v) := by
    have hp := (data.germs.piGerm i t ht0).self_of_nhds
    simpa only [orderedReverseLow, originalRadialReverseLow, jacobiAngularReverseLow] using canonicalLow_explicit_ordered_reverse_pairing
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t hSeg
      (ActualPiJacobiRadialGainedRows.piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        data.δ0 data.germs i t) hp.2.1 hp.2.2 v z
  refine ⟨?_, ?_, ?_⟩
  · intro a U
    cases a with
    | inl i => simpa only [angularAtomHigh, angularAtomLow] using hE i U
    | inr a =>
      cases a with
      | inl V => simpa only [angularAtomHigh, angularAtomLow] using generator_compat V U
      | inr i => simpa only [angularAtomHigh, angularAtomLow] using v017_inclusion_raisingHigh hF hO hD i U
  · intro a U
    cases a with
    | inl i => simpa only [angularAtomReverseHigh, angularAtomReverseLow] using hB i U
    | inr a =>
      cases a with
      | inl V => simpa only [angularAtomReverseHigh, angularAtomReverseLow] using generatorSharp_compat V U
      | inr i => simpa only [angularAtomReverseHigh, angularAtomReverseLow] using v017_inclusion_loweringHigh hF hO hD i U
  · intro a v z
    cases a with
    | inl i => simpa only [angularAtomLow, angularAtomReverseLow] using hP i v z
    | inr a =>
      cases a with
      | inl V => simpa only [angularAtomLow, angularAtomReverseLow] using generator_low_pivot V v z
      | inr i => simpa only [angularAtomLow, angularAtomReverseLow] using (v017_pairing_loweringLow_raisingLow hF hO hD i z v).symm

private theorem atom_smooth_on (d : ℝ) (hd : d ≤ data.δ) :
    ∀ a : AngularAtom,
      ContDiffOn ℝ ∞ (fun t => AH t a) (ParamRoom d) ∧
      ContDiffOn ℝ ∞ (fun t => AL t a) (ParamRoom d) ∧
      ContDiffOn ℝ ∞ (fun t => RH t a) (ParamRoom d) ∧
      ContDiffOn ℝ ∞ (fun t => RR t a) (ParamRoom d) := by
  have hSub : ParamRoom d ⊆ ParamRoom data.δ := fun t ht =>
    ⟨commonRoom_mono y0 ρ hd ht.1, ht.2⟩
  intro a
  cases a with
  | inl i =>
    simp only [angularAtomHigh, angularAtomLow, angularAtomReverseHigh, angularAtomReverseLow]
    exact ⟨((data.ordinary_smooth i).1).mono hSub,
      ((data.ordinary_smooth i).2.1).mono hSub,
      ((data.ordinary_smooth i).2.2.1).mono hSub,
      ((data.ordinary_smooth i).2.2.2).mono hSub⟩
  | inr a =>
    cases a with
    | inl V =>
      simp only [angularAtomHigh, angularAtomLow, angularAtomReverseHigh, angularAtomReverseLow]
      exact ⟨contDiffOn_const, contDiffOn_const, contDiffOn_const, contDiffOn_const⟩
    | inr i =>
      simp only [angularAtomHigh, angularAtomLow, angularAtomReverseHigh, angularAtomReverseLow]
      exact ⟨contDiffOn_const, contDiffOn_const, contDiffOn_const, contDiffOn_const⟩

private theorem generatorRaisingGainHigh_graph (V : Generator) (j : Fin 3) (U : Hi) :
    JL (generatorRaisingGainHigh hF hO hD V j U) =
      generatorSharpLow V (RA j U) - RL j (generatorSharpHigh V U) := by
  cases V with
  | inl ab =>
    have h := congrArg (fun A : Hi →L[ℝ] Neg => A U) (rotationRaisingHigh_graph hF hO hD ab.1 ab.2 j)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] at h
    simp only [generatorRaisingGainHigh, generatorSharpLow, generatorSharpHigh,
      generatorLow, generatorHigh, ContinuousLinearMap.neg_apply, map_neg]
    rw [h]
    abel
  | inr z =>
    simpa only [generatorRaisingGainHigh, generatorSharpLow, generatorSharpHigh,
      generatorHigh, generatorLow, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] using
      congrArg (fun A : Hi →L[ℝ] Neg => A U) (degreeRaisingHigh_graph hF hO hD j)

private theorem loweringGeneratorGainHigh_graph (i : Fin 3) (V : Generator) (U : Hi) :
    JL (loweringGeneratorGainHigh hF hO hD i V U) =
      LL i (generatorHigh V U) - generatorLow V (LA i U) := by
  cases V with
  | inl ab =>
    have h := congrArg (fun A : Hi →L[ℝ] Neg => A U) (rotationLoweringHigh_graph hF hO hD ab.1 ab.2 i)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] at h
    simp only [loweringGeneratorGainHigh, generatorLow, generatorHigh,
      ContinuousLinearMap.neg_apply, map_neg]
    rw [h]
    abel
  | inr z =>
    have h := congrArg (fun A : Hi →L[ℝ] Neg => A U) (degreeLoweringHigh_graph hF hO hD i)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.neg_apply, map_neg] at h
    simpa only [loweringGeneratorGainHigh, generatorLow, generatorHigh, neg_neg, neg_sub] using
      congrArg (fun n : Neg => -n) h

private theorem allAtomGainHigh_graph_at
    (left right : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half) (t : Tpar)
    (hEE : ∀ i j U, JL (GG i j t U) = BL i t (EH j t U) - EL j t (BH i t U))
    (hGenLeft : ∀ V j U, JL (PC hreg data.δ0 data.germs V j t U) =
      generatorSharpLow V (EH j t U) - EL j t (generatorSharpHigh V U))
    (hGenRight : ∀ V i U, JL (PD hreg data.δ0 data.germs V i t U) =
      BL i t (generatorHigh V U) - generatorLow V (BH i t U))
    (hLowerLeft : ∀ i j U, JL (left i j t U) = LL i (EH j t U) - EL j t (LA i U))
    (hLowerRight : ∀ i j U, JL (right i j t U) = BL j t (RA i U) - RL i (BH j t U))
    (a b : AngularAtom) (U : Hi) :
    JL (CG left right a b t U) = RR t a (AH t b U) - AL t b (RH t a U) := by
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      simpa only [allAtomGainHigh, angularAtomHigh, angularAtomLow,
        angularAtomReverseHigh, angularAtomReverseLow] using hEE i j U
    | inr b =>
      cases b with
      | inl V =>
        simpa only [allAtomGainHigh, angularAtomHigh, angularAtomLow,
          angularAtomReverseHigh, angularAtomReverseLow] using hGenRight V i U
      | inr j =>
        simpa only [allAtomGainHigh, angularAtomHigh, angularAtomLow,
          angularAtomReverseHigh, angularAtomReverseLow] using hLowerRight j i U
  | inr a =>
    cases a with
    | inl V =>
      cases b with
      | inl j =>
        simpa only [allAtomGainHigh, angularAtomHigh, angularAtomLow,
          angularAtomReverseHigh, angularAtomReverseLow] using hGenLeft V j U
      | inr b =>
        cases b with
        | inl W =>
          simpa only [allAtomGainHigh, angularAtomHigh, angularAtomLow,
            angularAtomReverseHigh, angularAtomReverseLow] using
            ActualFixedGeneratorPairedGains.fixedGeneratorGainHigh_graph V W U
        | inr j =>
          simpa only [allAtomGainHigh, angularAtomHigh, angularAtomLow,
            angularAtomReverseHigh, angularAtomReverseLow] using generatorRaisingGainHigh_graph hF hO hD V j U
    | inr i =>
      cases b with
      | inl j =>
        simpa only [allAtomGainHigh, angularAtomHigh, angularAtomLow,
          angularAtomReverseHigh, angularAtomReverseLow] using hLowerLeft i j U
      | inr b =>
        cases b with
        | inl V =>
          simpa only [allAtomGainHigh, angularAtomHigh, angularAtomLow,
            angularAtomReverseHigh, angularAtomReverseLow] using loweringGeneratorGainHigh_graph hF hO hD i V U
        | inr j =>
          simpa only [allAtomGainHigh, angularAtomHigh, angularAtomLow,
            angularAtomReverseHigh, angularAtomReverseLow] using gainedHigh_graph hF hO hD i j U

private theorem allAtomGainHigh_smooth_on
    (left right : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half) (d : ℝ)
    (hEE : ∀ i j, ContDiffOn ℝ ∞ (GG i j) (ParamRoom d))
    (hGenLeft : ∀ V j, ContDiffOn ℝ ∞ (PC hreg data.δ0 data.germs V j) (ParamRoom d))
    (hGenRight : ∀ V i, ContDiffOn ℝ ∞ (PD hreg data.δ0 data.germs V i) (ParamRoom d))
    (hLowerLeft : ∀ i j, ContDiffOn ℝ ∞ (left i j) (ParamRoom d))
    (hLowerRight : ∀ i j, ContDiffOn ℝ ∞ (right i j) (ParamRoom d))
    (a b : AngularAtom) :
    ContDiffOn ℝ ∞ (CG left right a b) (ParamRoom d) := by
  unfold allAtomGainHigh
  cases a with
  | inl i =>
    cases b with
    | inl j => exact hEE i j
    | inr b =>
      cases b with
      | inl V => exact hGenRight V i
      | inr j => exact hLowerRight j i
  | inr a =>
    cases a with
    | inl V =>
      cases b with
      | inl j => exact hGenLeft V j
      | inr b =>
        cases b with
        | inl W => exact contDiffOn_const
        | inr j => exact contDiffOn_const
    | inr i =>
      cases b with
      | inl j => exact hLowerLeft i j
      | inr b =>
        cases b with
        | inl V => exact contDiffOn_const
        | inr j => exact contDiffOn_const

private theorem gains_paired_of_graphs
    (t : Tpar) (C : AngularAtom → AngularAtom → Hi →L[ℝ] Half)
    (hA : ∀ a U, JL (AH t a U) = AL t a (IH U))
    (hB : ∀ a U, JL (RH t a U) = RR t a (IH U))
    (hP : ∀ a (v z : Half), PP v (AL t a z) = PP z (RR t a v))
    (hC : ∀ a b U, JL (C a b U) = RR t a (AH t b U) - AL t b (RH t a U))
    (a b : AngularAtom) (U V : Hi) :
    PP (IH V) (JL (C a b U)) = PP (IH U) (JL (C b a V)) := by
  have hForward (c : AngularAtom) (u : Hi) (x : Half) :
      PP (IH u) (AL t c x) = PP x (JL (RH t c u)) :=
    (hP c (IH u) x).trans (congrArg (PP x) (hB c u).symm)
  have hReverse (c : AngularAtom) (u : Hi) (x : Half) :
      PP (IH u) (RR t c x) = PP x (JL (AH t c u)) :=
    (hP c x (IH u)).symm.trans (congrArg (PP x) (hA c u).symm)
  have h1 : PP (IH V) (RR t a (AH t b U)) = PP (IH U) (RR t b (AH t a V)) :=
    (hReverse a V (AH t b U)).trans
      ((v016_pairing_inclusion_symm (AH t b U) (AH t a V)).trans (hReverse b U (AH t a V)).symm)
  have h2 : PP (IH V) (AL t b (RH t a U)) = PP (IH U) (AL t a (RH t b V)) :=
    (hForward b V (RH t a U)).trans
      ((v016_pairing_inclusion_symm (RH t a U) (RH t b V)).trans (hForward a U (RH t b V)).symm)
  have hL := (congrArg (fun n : Neg => PP (IH V) n) (hC a b U)).trans
    (v016_pairing_sub_right (IH V) _ _)
  have hR := (congrArg (fun n : Neg => PP (IH U) n) (hC b a V)).trans
    (v016_pairing_sub_right (IH U) _ _)
  exact hL.trans ((congrArg₂ (fun x y : ℝ => x-y) h1 h2).trans hR.symm)

/-- Complete high-packet prerequisite, including original geometry and every
actual high graph needed to derive the full low room. No cap callback is a field. -/
structure AllAngularAtomHighRoom (d : ℝ) where
  pos : 0 < d
  leData : d ≤ data.δ
  le0 : d ≤ data.δ0
  lerho : d ≤ ρ
  room : commonRoom y0 ρ d ⊆ Ω
  gainHigh : AngularAtom → AngularAtom → Tpar → Hi →L[ℝ] Half
  atomSmooth : ∀ a : AngularAtom,
    ContDiffOn ℝ ∞ (fun t => AH t a) (ParamRoom d) ∧
    ContDiffOn ℝ ∞ (fun t => AL t a) (ParamRoom d) ∧
    ContDiffOn ℝ ∞ (fun t => RH t a) (ParamRoom d) ∧
    ContDiffOn ℝ ∞ (fun t => RR t a) (ParamRoom d)
  gainSmooth : ∀ a b : AngularAtom, ContDiffOn ℝ ∞ (gainHigh a b) (ParamRoom d)
  atomGraph : ∀ a t, t ∈ ParamRoom d → ∀ U : Hi, JL (AH t a U) = AL t a (IH U)
  reverseAtomGraph : ∀ a t, t ∈ ParamRoom d → ∀ U : Hi, JL (RH t a U) = RR t a (IH U)
  atomPivot : ∀ a t, t ∈ ParamRoom d → ∀ v z : Half, PP v (AL t a z) = PP z (RR t a v)
  gainGraph : ∀ a b t, t ∈ ParamRoom d → ∀ U : Hi,
    JL (gainHigh a b t U) = RR t a (AH t b U) - AL t b (RH t a U)
  paired : ∀ a b t, t ∈ ParamRoom d → ∀ U V : Hi,
    PP (IH V) (JL (gainHigh a b t U)) = PP (IH U) (JL (gainHigh b a t V))
  retainedEEHigh : ∀ i j t, t ∈ ParamRoom d → gainHigh (Sum.inl i) (Sum.inl j) t = GG i j t

/-- Produce the complete original high prerequisite, separately from all
low selection, low E/E uniqueness, finite-cap summation and final room assembly. -/
theorem exists_same_packet_allAngularAtom_high_room (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, Nonempty (AllAngularAtomHighRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d) := by
  classical
  obtain ⟨dG, hdG, _hdG0, _hdGρ, _hRoomG, ⟨Gp⟩⟩ :=
    exists_retained_generator_paired_endpoints
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨dL, hdL, _hdL0, _hdLρ, _hRoomL, L0, R0, _Ll0, _Rl0,
      hSmLower, hLowerLeft, hLowerRight, _hLowerAdj, _hLowerLow, _hLowerCaps⟩ :=
    ActualLoweringEPairedEndpoints.exists_retained_lowering_E_paired_endpoints
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel data.δ0 data.δ0_pos data.germs
  let d := min data.δ (min dG dL)
  have hd : 0 < d := lt_min data.δ_pos (lt_min hdG hdL)
  have hdD : d ≤ data.δ := min_le_left _ _
  have hdG' : d ≤ dG := (min_le_right _ _).trans (min_le_left _ _)
  have hdL' : d ≤ dL := (min_le_right _ _).trans (min_le_right _ _)
  have hSubD := commonRoom_mono y0 ρ hdD
  have hSubG := commonRoom_mono y0 ρ hdG'
  have hSubL := commonRoom_mono y0 ρ hdL'
  have hPD : ParamRoom d ⊆ ParamRoom data.δ := fun t ht => ⟨hSubD ht.1, ht.2⟩
  have hPG : ParamRoom d ⊆ ParamRoom dG := fun t ht => ⟨hSubG ht.1, ht.2⟩
  have hPL : ParamRoom d ⊆ ParamRoom dL := fun t ht => ⟨hSubL ht.1, ht.2⟩
  let Ch : AngularAtom → AngularAtom → Tpar → Hi →L[ℝ] Half := CG L0 R0
  have hAtomSm := atom_smooth_on
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d hdD
  have hHighSm (aa bb : AngularAtom) : ContDiffOn ℝ ∞ (Ch aa bb) (ParamRoom d) := by
    simpa only [Ch] using allAtomGainHigh_smooth_on
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data L0 R0 d
      (fun i j => ((data.gained_smooth i j).1).mono hPD)
      (fun V j => (Gp.smoothLeft V j).mono hPG)
      (fun V i => (Gp.smoothRight V i).mono hPG)
      (fun i j => ((hSmLower i j).1).mono hPL)
      (fun i j => ((hSmLower i j).2.1).mono hPL) aa bb
  have hAtoms (t : Tpar) (ht : t ∈ ParamRoom d) := atom_facts_at
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data t (hPD ht)
  have hGraph (aa bb : AngularAtom) (t : Tpar) (ht : t ∈ ParamRoom d) (U : Hi) :
      JL (Ch aa bb t U) = RR t aa (AH t bb U) - AL t bb (RH t aa U) := by
    have hPR (V : Generator) (i : Fin 3) (Z : Hi) :
        JL (PD hreg data.δ0 data.germs V i t Z) =
          BL i t (generatorHigh V Z) - generatorLow V (BH i t Z) := by
      simpa only [ActualHigherSAdjointLeadingCoordinate.reverseEHigh_eq_ordered,
        ActualHigherSAdjointLeadingCoordinate.reverseELow_eq_ordered] using
        Gp.partnerGraph V i t (hPG ht) Z
    change JL (CG L0 R0 aa bb t U) = _
    exact allAtomGainHigh_graph_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data L0 R0 t
      (fun i j Z => data.high_graph i j t (hPD ht) Z)
      (fun V j Z => Gp.highGraph V j t (hPG ht) Z) hPR
      (fun i j Z => hLowerLeft i j t (hPL ht) Z)
      (fun i j Z => hLowerRight i j t (hPL ht) Z) aa bb U
  have hAdj (aa bb : AngularAtom) (t : Tpar) (ht : t ∈ ParamRoom d) (U V : Hi) :
      PP (IH V) (JL (Ch aa bb t U)) = PP (IH U) (JL (Ch bb aa t V)) :=
    gains_paired_of_graphs
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t
      (fun aa bb => Ch aa bb t) (hAtoms t ht).1 (hAtoms t ht).2.1 (hAtoms t ht).2.2
      (fun aa bb => hGraph aa bb t ht) aa bb U V
  refine ⟨d,⟨{
    pos := hd
    leData := hdD
    le0 := hdD.trans data.δ_le0
    lerho := hdD.trans data.δ_le
    room := hSubD.trans data.parameter_subset
    gainHigh := Ch
    atomSmooth := hAtomSm
    gainSmooth := hHighSm
    atomGraph := fun a t ht U => (hAtoms t ht).1 a U
    reverseAtomGraph := fun a t ht U => (hAtoms t ht).2.1 a U
    atomPivot := fun a t ht v z => (hAtoms t ht).2.2 a v z
    gainGraph := hGraph
    paired := hAdj
    retainedEEHigh := ?_ }⟩⟩
  intro i j t ht
  simp only [Ch,allAtomGainHigh]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomGainedRoom
