import Calderon.ActualLowerUSFirstAngularGainTranspose
import Calderon.ActualLowerUSIndexedAngularGraphs
import Calderon.ActualHigherSPhysicalPairing

/-! Author-support GPT-6.1 Sol. Before-code ../gained-jp-upfront-v001.md.
Actual gained quadratic J/E words and their TRUE reverse angular adjoints.
No compiler by author; authored imports await Root's coherent qualification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJPWords
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints ActualMixedAngularPairedGains
  ActualLowerUSSecondRow ActualLowerUSFirstAngularGainPair ActualHigherSPhysicalPairing
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private lemma pp_add_right (u : Half) (v z : Neg) :
    PP u (v+z) = PP u v+PP u z := by
  change ⟪u,v+z⟫_ℝ = ⟪u,v⟫_ℝ+⟪u,z⟫_ℝ
  exact inner_add_right u v z

private lemma pp_sub_right (u : Half) (v z : Neg) :
    PP u (v-z) = PP u v-PP u z := by
  change ⟪u,v-z⟫_ℝ = ⟪u,v⟫_ℝ-⟪u,z⟫_ℝ
  exact inner_sub_right u v z

private lemma pp_zero_right (u : Half) : PP u (0 : Neg) = 0 := by
  change ⟪u,(0 : Neg)⟫_ℝ = 0
  exact inner_zero_right u

private lemma pp_zero_left (v : Neg) : PP (0 : Half) v = 0 := by
  change ⟪(0 : Half),v⟫_ℝ = 0
  exact inner_zero_left v

private lemma firstword_graph (G Gs : Hi →L[ℝ] Half) (Gl Gsl : Half →L[ℝ] Neg)
    (E : Hi →L[ℝ] Half) (El : Half →L[ℝ] Neg)
    (hG : ∀ a b : Half, PP a (Gl b) = PP b (Gsl a))
    (hGs : ∀ a : Hi, Gsl (IH a) = JL (Gs a))
    (hE : ∀ a : Hi, JL (E a) = El (IH a))
    (u v us vg : Hi) (hu : IH us = Gs u) (hv : IH vg = G v) :
    PP (IH us) (JL (E v))-PP (IH u) (JL (E vg)) =
      PP (IH u) (Gl (E v)-El (G v)) := by
  have hLeft : PP (IH us) (JL (E v)) = PP (IH u) (Gl (E v)) := by
    calc
      _ = PP (Gs u) (JL (E v)) := congrArg (fun z : Half => PP z (JL (E v))) hu
      _ = PP (E v) (JL (Gs u)) := v016_pairing_inclusion_symm (Gs u) (E v)
      _ = PP (E v) (Gsl (IH u)) := congrArg (fun z : Neg => PP (E v) z) (hGs u).symm
      _ = _ := (hG (IH u) (E v)).symm
  have hRight : PP (IH u) (JL (E vg)) = PP (IH u) (El (G v)) :=
    congrArg (fun z : Neg => PP (IH u) z) ((hE vg).trans (congrArg El hv))
  calc
    _ = PP (IH u) (Gl (E v))-PP (IH u) (El (G v)) :=
      congrArg₂ (fun a b : ℝ => a-b) hLeft hRight
    _ = _ := (pp_sub_right (IH u) (Gl (E v)) (El (G v))).symm

private lemma quadratic_linear_graph
    (G1 G1s G2 G2s : Hi →L[ℝ] Half) (G1l G1sl G2l G2sl : Half →L[ℝ] Neg)
    (E C1 C2 : Hi →L[ℝ] Half) (El C1l : Half →L[ℝ] Neg)
    (hG1 : ∀ a b : Half, PP a (G1l b) = PP b (G1sl a))
    (hG2 : ∀ a b : Half, PP a (G2l b) = PP b (G2sl a))
    (hG1s : ∀ a : Hi, G1sl (IH a) = JL (G1s a))
    (hG2s : ∀ a : Hi, G2sl (IH a) = JL (G2s a))
    (hE : ∀ a : Hi, JL (E a) = El (IH a))
    (hC1 : ∀ a : Hi, JL (C1 a) = G1l (E a)-El (G1 a))
    (hC2 : ∀ a : Hi, JL (C2 a) = G2l (E a)-El (G2 a))
    (hC1up : ∀ a : Hi, C1l (IH a) = JL (C1 a))
    (u v u1 u21 v2 v12 : Hi)
    (hu1 : IH u1 = G1s u) (hu21 : IH u21 = G2s u1)
    (hv2 : IH v2 = G2 v) (hv12 : IH v12 = G1 v2) :
    PP (IH u21) (JL (E v))-PP (IH u) (JL (E v12)) =
      PP (IH u) ((G1l.comp C2+C1l.comp G2) v) := by
  have h2 : PP (IH u21) (JL (E v))-PP (IH u1) (JL (E v2)) =
      PP (IH u1) (JL (C2 v)) :=
    (firstword_graph G2 G2s G2l G2sl E El hG2 hG2s hE u1 v u21 v2 hu21 hv2).trans
      (congrArg (fun z : Neg => PP (IH u1) z) (hC2 v).symm)
  have h1 : PP (IH u1) (JL (E v2))-PP (IH u) (JL (E v12)) =
      PP (IH u) (JL (C1 v2)) :=
    (firstword_graph G1 G1s G1l G1sl E El hG1 hG1s hE u v2 u1 v12 hu1 hv12).trans
      (congrArg (fun z : Neg => PP (IH u) z) (hC1 v2).symm)
  have hLeft : PP (IH u1) (JL (C2 v)) = PP (IH u) (G1l (C2 v)) := by
    calc
      _ = PP (G1s u) (JL (C2 v)) := congrArg (fun z : Half => PP z (JL (C2 v))) hu1
      _ = PP (C2 v) (JL (G1s u)) := v016_pairing_inclusion_symm (G1s u) (C2 v)
      _ = PP (C2 v) (G1sl (IH u)) := congrArg (fun z : Neg => PP (C2 v) z) (hG1s u).symm
      _ = _ := (hG1 (IH u) (C2 v)).symm
  have hRight : PP (IH u) (JL (C1 v2)) = PP (IH u) (C1l (G2 v)) :=
    congrArg (fun z : Neg => PP (IH u) z) ((hC1up v2).symm.trans (congrArg C1l hv2))
  have h2' := h2.trans hLeft
  have h1' := h1.trans hRight
  change _ = PP (IH u) (G1l (C2 v)+C1l (G2 v))
  rw [pp_add_right]
  linarith only [h1',h2']

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GH" => firstAngularGainHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GL" => firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GS" => firstAngularGainSharpHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GSL" => firstAngularGainSharpLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "AH" => lowerSAngularHigh hF hO hD
local notation "AL" => lowerSAngularLow hF hO hD
local notation "ASH" => lowerSAngularSharpHigh hF hO hD
local notation "ASL" => lowerSAngularSharpLow hF hO hD

/-- Identity contributes the exact zero gain; the other branches use retained endpoints. -/
def jpGainHigh (mixed : MRoom) (j : Fin 3) (t : Tpar) : LowerCoreAngularGeneratorIndex → Hi →L[ℝ] Half
  | Sum.inl _ => 0
  | Sum.inr v => GH mixed j t v
def jpGainLow (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar) :
    LowerCoreAngularGeneratorIndex → Half →L[ℝ] Neg
  | Sum.inl _ => 0
  | Sum.inr v => GL mixed δ gen j t v
def jpGainSharpHigh (j : Fin 3) (t : Tpar) : LowerCoreAngularGeneratorIndex → Hi →L[ℝ] Half
  | Sum.inl _ => 0
  | Sum.inr v => GS j t v
def jpGainSharpLow (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar) :
    LowerCoreAngularGeneratorIndex → Half →L[ℝ] Neg
  | Sum.inl _ => 0
  | Sum.inr v => GSL mixed δ gen j t v
local notation "CH" => jpGainHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "CL" => jpGainLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "CSH" => jpGainSharpHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "CSL" => jpGainSharpLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

private lemma E_upper (j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom data.δ) (u : Hi) :
    JL (EH j t u) = EL j t (IH u) := by
  have ht0 : t ∈ ParamRoom data.δ0 := ⟨commonRoom_mono y0 ρ data.δ_le0 ht.1,ht.2⟩
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData data.parameter_subset t.1 ht.1
  have hp := (data.germs.piGerm j t ht0).self_of_nhds
  exact canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg j t hSeg _ hp.1 hp.2.1 u

lemma jpGainHigh_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ) (htD : t ∈ ParamRoom data.δ)
    (i : LowerCoreAngularGeneratorIndex) (u : Hi) :
    JL (CH mixed j t i u) = AL i (EH j t u)-EL j t (AH i u) := by
  cases i with
  | inl z =>
    simp only [jpGainHigh,lowerSAngularLow,lowerSAngularHigh,ContinuousLinearMap.zero_apply,map_zero]
    exact (sub_eq_zero.mpr (E_upper g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data j t htD u)).symm
  | inr v =>
    exact firstAngularGainHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 Room hreg data mixed δ gen j t htG htM v u

lemma jpGain_upper (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (i : LowerCoreAngularGeneratorIndex) (u : Hi) :
    CL mixed δ gen j t i (IH u) = JL (CH mixed j t i u) := by
  cases i with
  | inl z => simp only [jpGainLow,jpGainHigh,ContinuousLinearMap.zero_apply,map_zero]
  | inr v =>
    exact (firstAngularGain_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen j t htG htM v u).trans
      (firstAngularGainHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data mixed δ gen j t htG htM v u).symm

private lemma gain_pair (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (i : LowerCoreAngularGeneratorIndex) (u : Hi) (z : Half) :
    PP (IH u) (CL mixed δ gen j t i z) = PP (CSH j t i u) (JL z) := by
  cases i with
  | inl a =>
    change PP (IH u) (0 : Neg) = PP (0 : Half) (JL z)
    exact (pp_zero_right (IH u)).trans (pp_zero_left (JL z)).symm
  | inr v =>
    exact firstAngularGain_low_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen j t htG htM v u z

private lemma gain_star_pair (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (i : LowerCoreAngularGeneratorIndex) (u : Hi) (z : Half) :
    PP (IH u) (CSL mixed δ gen j t i z) = PP (CH mixed j t i u) (JL z) := by
  cases i with
  | inl a =>
    change PP (IH u) (0 : Neg) = PP (0 : Half) (JL z)
    exact (pp_zero_right (IH u)).trans (pp_zero_left (JL z)).symm
  | inr v =>
    change PP (IH u) (sphereLowerDistributionalTranspose (GL mixed δ gen j t v) z) = _
    rw [← sphereSobolevDualPairing_lower_distributionalTranspose]
    have hu := jpGain_upper g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen j t htG htM (Sum.inr v) u
    change GL mixed δ gen j t v (IH u) = JL (GH mixed j t v u) at hu
    exact (congrArg (fun y : Neg => PP z y) hu).trans
      (v016_pairing_inclusion_symm z (GH mixed j t v u))

/-- Complete forward or TRUE adjoint gained quadratic-word/E coefficient. -/
def quadraticEWord (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) : Hi →L[ℝ] Neg :=
  if adjoint then (CSL mixed δ gen j t ij.2).comp (ASH ij.1) + (ASL ij.2).comp (CSH j t ij.1)
  else (AL ij.1).comp (CH mixed j t ij.2) + (CL mixed δ gen j t ij.1).comp (AH ij.2)
local notation "QW" => quadraticEWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

lemma quadraticEWord_pairing (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) (u v : Hi) :
    PP (IH u) (QW false mixed δ gen j t ij v) = PP (IH v) (QW true mixed δ gen j t ij u) := by
  have hGen (i : LowerCoreAngularGeneratorIndex) (a : Hi) (z : Half) :
      PP (IH a) (AL i z) = PP (ASH i a) (JL z) := by
    rw [lowerSAngularLow_pairing,← lowerSAngularSharpHigh_low_compatibility]
    exact v016_pairing_inclusion_symm _ _
  have hGenStar (i : LowerCoreAngularGeneratorIndex) (a : Hi) (z : Half) :
      PP (IH a) (ASL i z) = PP (AH i a) (JL z) := by
    rw [lowerSAngularSharpLow_pairing,← lowerSAngularHigh_low_compatibility]
    exact v016_pairing_inclusion_symm _ _
  have hA : PP (IH u) (AL ij.1 (CH mixed j t ij.2 v)) =
      PP (IH v) (CSL mixed δ gen j t ij.2 (ASH ij.1 u)) := by
    calc
      _ = PP (ASH ij.1 u) (JL (CH mixed j t ij.2 v)) := hGen ij.1 u _
      _ = PP (CH mixed j t ij.2 v) (JL (ASH ij.1 u)) := v016_pairing_inclusion_symm _ _
      _ = _ := (gain_star_pair g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data mixed δ gen j t htG htM ij.2 v _).symm
  have hB : PP (IH u) (CL mixed δ gen j t ij.1 (AH ij.2 v)) =
      PP (IH v) (ASL ij.2 (CSH j t ij.1 u)) := by
    calc
      _ = PP (CSH j t ij.1 u) (JL (AH ij.2 v)) := gain_pair
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
          mixed δ gen j t htG htM ij.1 u _
      _ = PP (AH ij.2 v) (JL (CSH j t ij.1 u)) := v016_pairing_inclusion_symm _ _
      _ = _ := (hGenStar ij.2 v _).symm
  simp only [quadraticEWord,Bool.false_eq_true,if_false,if_true,add_apply,
    ContinuousLinearMap.comp_apply,pp_add_right]
  exact congrArg₂ (fun a b : ℝ => a+b) hA hB

/-- Genuine finite pretest graph; no E output is asserted finite. -/
lemma quadraticEWord_physical_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ) (htD : t ∈ ParamRoom data.δ)
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex)
    (U V : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪(lowerQuadraticWordAdjoint hO hD hF ij U).val x,
      sphereSobolevHalfToSphereL2L hO hD (EH j t (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x))⟫_ℝ -
    ⟪U.val x,sphereSobolevHalfToSphereL2L hO hD
      (EH j t (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerQuadraticWord hO hD hF ij V) x))⟫_ℝ =
    PP (finiteCoreSobolevLift hO hD (1/2 : ℝ) U x)
      (QW false mixed δ gen j t ij (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) := by
  have hP1 := finiteCore_halfPairing_eq_inner hO hD
    (lowerQuadraticWordAdjoint hO hD hF ij U)
    (EH j t (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) x
  have hP2 := finiteCore_halfPairing_eq_inner hO hD U
    (EH j t (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerQuadraticWord hO hD hF ij V) x)) x
  have hGeneric := quadratic_linear_graph
    (AH ij.1) (ASH ij.1) (AH ij.2) (ASH ij.2)
    (AL ij.1) (ASL ij.1) (AL ij.2) (ASL ij.2)
    (EH j t) (CH mixed j t ij.1) (CH mixed j t ij.2) (EL j t) (CL mixed δ gen j t ij.1)
    (lowerSAngularLow_pairing hF hO hD ij.1) (lowerSAngularLow_pairing hF hO hD ij.2)
    (fun a => (lowerSAngularSharpHigh_low_compatibility hF hO hD ij.1 a).symm)
    (fun a => (lowerSAngularSharpHigh_low_compatibility hF hO hD ij.2 a).symm)
    (E_upper g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data j t htD)
    (jpGainHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ gen j t htG htM htD ij.1)
    (jpGainHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ gen j t htG htM htD ij.2)
    (jpGain_upper g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ gen j t htG htM ij.1)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerCoreAngularGeneratorAdjoint hO hD hF ij.1 U) x)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerQuadraticWordAdjoint hO hD hF ij U) x)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerCoreAngularGenerator hO hD hF ij.2 V) x)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerQuadraticWord hO hD hF ij V) x)
    (lowerSAngularSharpHigh_finiteCoreHi_inclusion hF hO hD ij.1 U x)
    (lowerSAngularSharpHigh_finiteCoreHi_inclusion hF hO hD ij.2
      (lowerCoreAngularGeneratorAdjoint hO hD hF ij.1 U) x)
    (lowerSAngularHigh_finiteCoreHi_inclusion hF hO hD ij.2 V x)
    (lowerSAngularHigh_finiteCoreHi_inclusion hF hO hD ij.1
      (lowerCoreAngularGenerator hO hD hF ij.2 V) x)
  calc
    _ = PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerQuadraticWordAdjoint hO hD hF ij U) x))
          (JL (EH j t (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x))) -
        PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
          (JL (EH j t (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerQuadraticWord hO hD hF ij V) x))) :=
      congrArg₂ (fun a b : ℝ => a-b) hP1.symm hP2.symm
    _ = PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
        (QW false mixed δ gen j t ij (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) := hGeneric
    _ = _ := congrArg
      (fun y : Half => PP y (QW false mixed δ gen j t ij (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)))
      (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U x)

/-- A fixed, explicit ordinary generator budget, independent of every profile. -/
def jpOrdinaryGeneratorBudget : ℝ :=
  1+(∑ i : LowerCoreAngularGeneratorIndex, (‖AH i‖+‖AL i‖+‖ASH i‖+‖ASL i‖))

lemma jpOrdinaryGeneratorBudget_pos : 0 < jpOrdinaryGeneratorBudget hF hO hD := by
  unfold jpOrdinaryGeneratorBudget
  positivity

lemma jpOrdinaryGeneratorBudget_bounds (i : LowerCoreAngularGeneratorIndex) :
    ‖AH i‖ ≤ jpOrdinaryGeneratorBudget hF hO hD ∧
    ‖AL i‖ ≤ jpOrdinaryGeneratorBudget hF hO hD ∧
    ‖ASH i‖ ≤ jpOrdinaryGeneratorBudget hF hO hD ∧
    ‖ASL i‖ ≤ jpOrdinaryGeneratorBudget hF hO hD := by
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun k : LowerCoreAngularGeneratorIndex => ‖AH k‖+‖AL k‖+‖ASH k‖+‖ASL k‖)
    (fun k _ => by positivity) (Finset.mem_univ i)
  unfold jpOrdinaryGeneratorBudget
  constructor
  · nlinarith [norm_nonneg (AL i),norm_nonneg (ASH i),norm_nonneg (ASL i)]
  constructor
  · nlinarith [norm_nonneg (AH i),norm_nonneg (ASH i),norm_nonneg (ASL i)]
  constructor
  · nlinarith [norm_nonneg (AH i),norm_nonneg (AL i),norm_nonneg (ASL i)]
  · nlinarith [norm_nonneg (AH i),norm_nonneg (AL i),norm_nonneg (ASH i)]

/-- All four actual gained endpoints have one retained cap; the identity case
is zero. This is a mechanical wrapper of the genuine room producer's data. -/
lemma jpGain_caps (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ v : FirstAngularIndex, ‖GL mixed δ gen j t v‖ ≤ M ∧ ‖GH mixed j t v‖ ≤ M ∧
      ‖GS j t v‖ ≤ M ∧ ‖GSL mixed δ gen j t v‖ ≤ M)
    (i : LowerCoreAngularGeneratorIndex) :
    ‖CL mixed δ gen j t i‖ ≤ M ∧ ‖CH mixed j t i‖ ≤ M ∧
      ‖CSH j t i‖ ≤ M ∧ ‖CSL mixed δ gen j t i‖ ≤ M := by
  cases i with
  | inl z => simpa only [jpGainLow,jpGainHigh,jpGainSharpHigh,jpGainSharpLow,ContinuousLinearMap.opNorm_zero] using
      (show (0:ℝ) ≤ M ∧ 0 ≤ M ∧ 0 ≤ M ∧ 0 ≤ M from ⟨hM,hM,hM,hM⟩)
  | inr v => exact h v

lemma norm_quadraticEWord_le (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ v : FirstAngularIndex, ‖GL mixed δ gen j t v‖ ≤ M ∧ ‖GH mixed j t v‖ ≤ M ∧
      ‖GS j t v‖ ≤ M ∧ ‖GSL mixed δ gen j t v‖ ≤ M)
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
    ‖QW adjoint mixed δ gen j t ij‖ ≤ 2*jpOrdinaryGeneratorBudget hF hO hD*M := by
  have hMG := (jpOrdinaryGeneratorBudget_pos hF hO hD).le
  have h1 := jpGain_caps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ gen j t M hM h ij.1
  have h2 := jpGain_caps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ gen j t M hM h ij.2
  have hG1 := jpOrdinaryGeneratorBudget_bounds hF hO hD ij.1
  have hG2 := jpOrdinaryGeneratorBudget_bounds hF hO hD ij.2
  cases adjoint
  · change ‖(AL ij.1).comp (CH mixed j t ij.2)+(CL mixed δ gen j t ij.1).comp (AH ij.2)‖ ≤ _
    have hb1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hG1.2.1 h2.2.1 (norm_nonneg _) hMG)
    have hb2 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h1.1 hG2.1 (norm_nonneg _) hM)
    nlinarith only [(norm_add_le _ _).trans (add_le_add hb1 hb2)]
  · change ‖(CSL mixed δ gen j t ij.2).comp (ASH ij.1)+(ASL ij.2).comp (CSH j t ij.1)‖ ≤ _
    have hb1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h2.2.2.2 hG1.2.2.1 (norm_nonneg _) hM)
    have hb2 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hG2.2.2.2 h1.2.2.1 (norm_nonneg _) hMG)
    nlinarith only [(norm_add_le _ _).trans (add_le_add hb1 hb2)]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJPWords
