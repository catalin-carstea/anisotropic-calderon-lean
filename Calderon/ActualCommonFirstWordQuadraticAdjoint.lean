import Calderon.ActualReverseEHigherLift
import Calderon.ActualHigherSPhysicalPairing

/-! The common first-word/quadratic adjoint. On any retained `W`: one common room `δ` (native
reverse room ∩ forward generator graph ∩ forward generator germs), rebuilt forward canonical
ambient germs / compatibility / genuine pivot on that W; global forward (`higherSLift`) and
reverse (`reverseEHigherLift`) Hi lifts under the membership-only premise; the quadratic double
angular Half fields `FwdDouble = higherSDoubleHalf` and `RevDouble = R^3 Σ Q_ij e_j(Tx)(VR_i)`;
and the exact pointwise and integrated physical adjoint identity. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCommonFirstWordQuadraticAdjoint
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private lemma inner_weighted_double_sum {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : H →L[ℝ] E) (c : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (u v : E) (f g : Fin 3 → Fin 3 → H)
    (h : ∀ i j, ⟪u,K (f i j)⟫_ℝ = ⟪K (g i j),v⟫_ℝ) :
    ⟪u,K (c • ∑ i : Fin 3, ∑ j : Fin 3, Q i j • f i j)⟫_ℝ =
      ⟪K (c • ∑ i : Fin 3, ∑ j : Fin 3, Q i j • g i j),v⟫_ℝ := by
  simp only [map_smul,map_sum,inner_smul_right,real_inner_smul_left,inner_sum,sum_inner,h]

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
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CGE" => generatorEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "RevRoom" => ActualReverseEHigherLift.ReverseERoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-! ## 1. Forward canonical germs, compatibility and genuine pivot on ANY retained W -/

/-- Ambient germs of `E_i = Th∘PiH_i + Σ raisingHigh∘NH + IH∘ZH_i` and of `EL_i` at every
point of the closed room, from the neighbourhood W Pi/Jacobi germs, common-support native
multipliers, the actual adjoint radial remainder on the segment and the native zero correction. -/
theorem canonical_ambient_contDiffAt (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0) (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
    ContDiffAt ℝ ∞ (EH i) t ∧ ContDiffAt ℝ ∞ (EL i) t := by
  have ht0 : t ∈ ParamRoom δ0 := ⟨hSub ht.1, ht.2⟩
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
  have hRem := contDiffAt_actualAngularRadialRemainder_families_of_segment
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg
  have hTh : ContDiffAt ℝ ∞ (fun s : Tpar => Th s.1) t :=
    hRem.1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  have hTl : ContDiffAt ℝ ∞ (fun s : Tpar => Tl s.1) t := by
    first
      | exact hRem.2.1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
      | exact hRem.2.2.2.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  -- Pi germs from the actual neighbourhood W.piGerm
  have hPi := ActualFullEZeroRowsSmoothGerms.commonSupport_native_contDiffAt hcalc hF hO hD τ0
    (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i) t
  have hPiGerm := W.piGerm i t ht0
  have hPiH : ContDiffAt ℝ ∞ (PiH i) t :=
    hPi.1.congr_of_eventuallyEq (hPiGerm.mono (fun z hz => hz.1.symm))
  have hPiL : ContDiffAt ℝ ∞ (PiL i) t :=
    hPi.2.1.congr_of_eventuallyEq (hPiGerm.mono (fun z hz => hz.2.1.symm))
  -- Jacobi germs from the actual neighbourhood W.jacobiGerm
  have hNp (m : Fin 3) :
      ContDiffAt ℝ ∞ (fun z : Pphys => NH (NJ3 i m z)) t.1 ∧
      ContDiffAt ℝ ∞ (fun z : Pphys => NL (NJ2 i m z)) t.1 := by
    have hs := ActualFullEZeroRowsSmoothGerms.commonSupport_native_contDiffAt hcalc hF hO hD τ0
      (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m) (W.jacobiCompact i m)
      (W.jacobiZero i m) t.1
    have hgerm := W.jacobiGerm i m t.1 ht0.1
    exact ⟨hs.1.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.1.symm)),
      hs.2.1.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.1.symm))⟩
  have hNH (m : Fin 3) : ContDiffAt ℝ ∞ (fun s : Tpar => NH (NJ3 i m s.1)) t :=
    (hNp m).1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  have hNL (m : Fin 3) : ContDiffAt ℝ ∞ (fun s : Tpar => NL (NJ2 i m s.1)) t :=
    (hNp m).2.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  -- native zero correction rows
  have hProj : ContDiff ℝ ∞ (fun z : Tpar => (z.1.1,z.1.2.1)) :=
    contDiff_fst.fst.prodMk contDiff_fst.snd.fst
  have hDr (s : ℝ) : ContDiffAt ℝ ∞ (fun z : Tpar =>
      sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L z.1.1 z.1.2.1)) t :=
    ((contDiff_reference_sphereSobolevRadialDriftAdjointL g hg L hF hO hD s).comp hProj).contDiffAt
  have hr : ContDiffAt ℝ ∞ (fun z : Tpar => z.1.2.2) t := contDiffAt_fst.snd.snd
  have hZH : ContDiffAt ℝ ∞ (fun s : Tpar => ZH i s.1) t :=
    hr.smul (ContDiffAt.sum (fun m _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNH m))))
  have hZL : ContDiffAt ℝ ∞ (fun s : Tpar => ZL i s.1) t :=
    hr.smul (ContDiffAt.sum (fun m _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNL m))))
  refine ⟨?_, ?_⟩
  · exact ((hTh.clm_comp hPiH).add
      (ContDiffAt.sum (fun m _ => contDiffAt_const.clm_comp (hNH m)))).add
        (contDiffAt_const.clm_comp hZH)
  · exact ((hTl.clm_comp hPiL).add
      (ContDiffAt.sum (fun m _ => contDiffAt_const.clm_comp (hNL m)))).add
        (contDiffAt_const.clm_comp hZL)

/-- Forward high/low compatibility on ANY W, from `W.piGerm` and the actual segment. -/
theorem canonical_compat_anyW (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0) (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u : Hi) :
    JL (EH i t u) = EL i t (IH u) := by
  have hp := (W.piGerm i t ⟨hSub ht.1, ht.2⟩).self_of_nhds
  exact canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg i t
    (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1)
    (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W i t) hp.1 hp.2.1 u

/-- Genuine pivot `PP(E_i u, J I v) = PP(I u, J e_i v)` on ANY W, `e_i` the public reverse. -/
theorem canonical_reverse_pivot_anyW (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0) (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u v : Hi) :
    PP (EH i t u) (JL (IH v)) = PP (IH u) (JL (eH i t v)) := by
  have hp := (W.piGerm i t ⟨hSub ht.1, ht.2⟩).self_of_nhds
  have h := canonicalHigh_genuine_ordered_reverse_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg i t
    (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1)
    (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W i t) hp.1 hp.2.1 hp.2.2 u v
  first
    | exact h
    | simpa only [reverseEHigh] using h

/-- The native reverse room restricts to every smaller positive radius. -/
theorem reverseERoom_mono (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    {δ δ' : ℝ} (R : RevRoom hreg δ0 W δ) (hpos : 0 < δ') (hle : δ' ≤ δ) :
    RevRoom hreg δ0 W δ' := by
  have hS := commonRoom_mono y0 ρ hle
  exact {
    pos := hpos
    le0 := hle.trans R.le0
    leρ := hle.trans R.leρ
    room := hS.trans R.room
    germHigh := fun j t ht => R.germHigh j t ⟨hS ht.1, ht.2⟩
    germLow := fun j t ht => R.germLow j t ⟨hS ht.1, ht.2⟩
    germGen := fun V j t ht => R.germGen V j t ⟨hS ht.1, ht.2⟩
    graph := fun V j t ht u => R.graph V j t ⟨hS ht.1, ht.2⟩ u
    compat := fun j t ht u => R.compat j t ⟨hS ht.1, ht.2⟩ u }

/-- One common room on the caller's W: native reverse room, forward canonical germs and
compatibility, forward generator graph and germs, genuine pivot. -/
structure CommonFirstWordRoom (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) : Prop where
  rev : RevRoom hreg δ0 W δ
  germHigh : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (EH i) t
  germLow : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (EL i) t
  compat : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (EH i t u) = EL i t (IH u)
  genGraph : ∀ V : Generator, ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
    JL (CGE hreg δ0 W V j t u) = generatorLow V (EH j t u) - EL j t (generatorHigh V u)
  genGerm : ∀ V : Generator, ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (CGE hreg δ0 W V j) t
  pivot : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u v : Hi,
    PP (EH i t u) (JL (IH v)) = PP (IH u) (JL (eH i t v))
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Producer on ANY retained W: intersect the three native rooms; no new W. -/
theorem exists_common_first_word_room (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, CRoom hreg δ0 W δ := by
  obtain ⟨dR, R⟩ := ActualReverseEHigherLift.exists_retained_reverseE_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  obtain ⟨d1, hd1, _hd10, _hd1ρ, hG⟩ :=
    ActualGeneratorEHighGainedGraph.exists_commonRoom_actual_generator_E_high_graphs
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg hKernel δ0 hδ0 W
  obtain ⟨d2, hd2, _hd20, _hd2ρ, hC⟩ :=
    ActualGeneratorEHighSmoothGerms.exists_commonRoom_actual_generator_E_high_contDiffAt
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg δ0 hδ0 W
  have hδ : 0 < min dR (min d1 d2) := lt_min R.pos (lt_min hd1 hd2)
  have hδR : min dR (min d1 d2) ≤ dR := min_le_left _ _
  have hδ1 : min dR (min d1 d2) ≤ d1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : min dR (min d1 d2) ≤ d2 := (min_le_right _ _).trans (min_le_right _ _)
  have R' := reverseERoom_mono g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W R hδ hδR
  have hSub0 : commonRoom y0 ρ (min dR (min d1 d2)) ⊆ commonRoom y0 ρ δ0 :=
    commonRoom_mono y0 ρ R'.le0
  have hS1 := commonRoom_mono y0 ρ hδ1
  have hS2 := commonRoom_mono y0 ρ hδ2
  exact ⟨min dR (min d1 d2), {
    rev := R'
    germHigh := fun i t ht => (canonical_ambient_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W _ hSub0 R'.room i t ht).1
    germLow := fun i t ht => (canonical_ambient_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W _ hSub0 R'.room i t ht).2
    compat := fun i t ht u => canonical_compat_anyW g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W _ hSub0 R'.room i t ht u
    genGraph := fun V j t ht u => hG V j t ⟨hS1 ht.1, ht.2⟩ u
    genGerm := fun V j t ht => hC V j t ⟨hS2 ht.1, ht.2⟩
    pivot := fun i t ht u v => canonical_reverse_pivot_anyW g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W _ hSub0 R'.room i t ht u v }⟩

/-! ## 2. Global first-word lifts on all of R3 (membership-only premise) -/

/-- Compact support from vanishing off the compact input support. -/
lemma hasCompactSupport_of_eq_zero_off {E : Type*} [TopologicalSpace E] [Zero E]
    (F0 : smoothCompactFiniteSphereCore hO hD) (f : R3 → E) (hf : ∀ z ∉ TS F0, f z = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro F0.property.2.1 hf

/-- GLOBAL forward inclusion `IH VF_j = E_j(Tx) U(x)`. -/
theorem fwdLift_inclusion (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (j : Fin 3) (x : R3) :
    IH (VF δr Ar p q hreg δ0 W F0 j x) = EH j ((Tq δr Ar p q) x) (Uin F0 x) := by
  by_cases hx : x ∈ TS F0
  · exact ActualHigherSFormation.higherSLift_inclusion_of_graph hF hO hD g L y0 Φ B ε C ρ H a w
      hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W F0 j x
      (fun v => Cm.genGraph (Sum.inr ()) j _ (hT x hx) v) (fun v => Cm.compat j _ (hT x hx) v)
  · have h1 := ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData
      hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W F0 j x hx
    have h2 := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData
      hg hcalc τ0 δr Ar p hδr hAr q F0 x hx
    simp only [h1, h2, map_zero]

/-- GLOBAL C^∞ of the forward lift via the membership-only family glue. -/
theorem contDiff_fwdLift (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (j : Fin 3) :
    ContDiff ℝ ∞ (VF δr Ar p q hreg δ0 W F0 j) := by
  have hU := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hUB := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F0)
  have hU0 := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q F0
  have hUB0 := ActualHigherSFormation.higherSDegreeInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q F0
  have h1 := ActualHigherSFormation.contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q (CGE hreg δ0 W (Sum.inr ()) j) F0
    (fun x hx => Cm.genGerm (Sum.inr ()) j _ (hT x hx)) (Uin F0) hU hU0
  have h2 := ActualHigherSFormation.contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q (EH j) F0
    (fun x hx => Cm.germHigh j _ (hT x hx))
    (ActualHigherSFormation.higherSDegreeInput hO hD F0) hUB hUB0
  have h3 := ActualHigherSFormation.contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q (EH j) F0
    (fun x hx => Cm.germHigh j _ (hT x hx)) (Uin F0) hU hU0
  exact (sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)).contDiff.comp ((h1.add h2).add h3)

/-- Full common first-word lift contract on one `δ` fixed before every profile. -/
def CommonFirstWordLiftContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) : Prop :=
  ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → 0 < Ar → ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 →
  ∀ F0 : smoothCompactFiniteSphereCore hO hD,
    (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) → ∀ j : Fin 3,
      (∀ x : R3, IH (VF δr Ar p q hreg δ0 W F0 j x) = EH j ((Tq δr Ar p q) x) (Uin F0 x)) ∧
      ContDiff ℝ ∞ (VF δr Ar p q hreg δ0 W F0 j) ∧
      (∀ z ∉ TS F0, VF δr Ar p q hreg δ0 W F0 j z = 0) ∧
      HasCompactSupport (VF δr Ar p q hreg δ0 W F0 j) ∧
      (∀ x : R3, IH (VR hreg δ0 W δr Ar p q F0 j x) = eH j ((Tq δr Ar p q) x) (Uin F0 x)) ∧
      ContDiff ℝ ∞ (VR hreg δ0 W δr Ar p q F0 j) ∧
      (∀ z ∉ TS F0, VR hreg δ0 W δr Ar p q F0 j z = 0) ∧
      HasCompactSupport (VR hreg δ0 W δr Ar p q F0 j)

theorem commonFirstWordLiftContract_of_room (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    CommonFirstWordLiftContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ := by
  intro δr Ar p hδr hAr q _hq F0 hT j
  have hV0 := ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W F0 j
  have hR0 := ActualReverseEHigherLift.reverseEHigherLift_eq_zero g L y0 Φ B ε C ρ H a w hData hg
    hcalc hF hO hD τ0 hreg δ0 W δr Ar p q F0 j
  exact ⟨fwdLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
      δr Ar p hδr hAr q F0 hT j,
    contDiff_fwdLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
      δr Ar p hδr hAr q F0 hT j,
    hV0,
    hasCompactSupport_of_eq_zero_off hO hD F0 _ hV0,
    ActualReverseEHigherLift.reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm.rev δr Ar p q F0 hT j,
    ActualReverseEHigherLift.contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm.rev δr Ar p hδr hAr q F0 hT j,
    hR0,
    hasCompactSupport_of_eq_zero_off hO hD F0 _ hR0⟩

/-! ## 3. Quadratic double angular Half fields -/

/-- Genuine reverse double field, reversed order `e_j(Tx)(VR_i)`. -/
def revDoubleHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (x : R3) : Half :=
  (referenceRadius δr Ar p L x)^3 • (∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
      eH j ((Tq δr Ar p q) x) (VR hreg δ0 W δr Ar p q F0 i x))
local notation "RD" => revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Literal identification of the EXACT forward double field. -/
theorem fwdDouble_eq (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (x : R3) :
    FD δr Ar p q hreg δ0 W g2 F0 x = (referenceRadius δr Ar p L x)^3 • (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
        EH i ((Tq δr Ar p q) x) (VF δr Ar p q hreg δ0 W F0 j x)) := rfl

theorem fwdDouble_eq_zero (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3) (hz : z ∉ TS F0) :
    FD δr Ar p q hreg δ0 W g2 F0 z = 0 := by
  have hV0 (j : Fin 3) := ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W F0 j z hz
  rw [fwdDouble_eq g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0]
  simp only [hV0, map_zero, smul_zero, Finset.sum_const_zero]

theorem revDouble_eq_zero (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3) (hz : z ∉ TS F0) :
    RD hreg δ0 W g2 δr Ar p q F0 z = 0 := by
  have hR0 (i : Fin 3) := ActualReverseEHigherLift.reverseEHigherLift_eq_zero g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δr Ar p q F0 i z hz
  simp only [revDoubleHalf, hR0, map_zero, smul_zero, Finset.sum_const_zero]

lemma contDiff_frameCoefficient (hgA : IsAdmissibleMetric g) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (q : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun y : R3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) :=
  (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hgA hg2 L i j).comp
    (f := fun y : R3 => (q,y)) (contDiff_const.prodMk contDiff_id)

theorem contDiff_fwdDouble (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (FD δr Ar p q hreg δ0 W g2 F0) := by
  have hRR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hV (j : Fin 3) := contDiff_fwdLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hT j
  have hV0 (j : Fin 3) := ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W F0 j
  have hQ := contDiff_frameCoefficient g L hg g2 hg2 q
  have hEV (i j : Fin 3) : ContDiff ℝ ∞
      (fun y => EH i ((Tq δr Ar p q) y) (VF δr Ar p q hreg δ0 W F0 j y)) :=
    ActualHigherSFormation.contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q (EH i) F0 (fun x hx => Cm.germHigh i _ (hT x hx))
      (VF δr Ar p q hreg δ0 W F0 j) (hV j) (hV0 j)
  exact (hRR.pow 3).smul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (hQ i j).smul (hEV i j))))

theorem contDiff_revDouble (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (RD hreg δ0 W g2 δr Ar p q F0) := by
  have hRR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hTs := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q
  have hVR (i : Fin 3) := ActualReverseEHigherLift.contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm.rev δr Ar p hδr hAr q F0 hT i
  have hVR0 (i : Fin 3) := ActualReverseEHigherLift.reverseEHigherLift_eq_zero g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δr Ar p q F0 i
  have hQ := contDiff_frameCoefficient g L hg g2 hg2 q
  have hEV (j i : Fin 3) : ContDiff ℝ ∞
      (fun y => eH j ((Tq δr Ar p q) y) (VR hreg δ0 W δr Ar p q F0 i y)) :=
    ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
      (fun x hx => Cm.rev.germHigh j _ (hT x hx)) (VR hreg δ0 W δr Ar p q F0 i) (hVR i) (hVR0 i)
  exact (hRR.pow 3).smul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (hQ i j).smul (hEV j i))))

/-! ## 4. Exact physical adjoint -/

attribute [local irreducible] canonicalHigh canonicalLow reverseEHigh reverseELow
  sphereSobolevInclusionL sphereSobolevDualPairing sphereSobolevHalfToSphereL2L
  ActualHigherSFormation.higherSLift ActualReverseEHigherLift.reverseEHigherLift
  ActualHigherSFormation.higherSDoubleHalf revDoubleHalf

/-- Generic one-row identity at a common room point: the true reversal `e_j e_i`. -/
theorem one_row_physical_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (t : Tpar) (ht : t ∈ ParamRoom δ) (i j : Fin 3)
    (u v wv ru : Hi) (hw : IH wv = EH j t v) (hr : IH ru = eH i t u) :
    ⟪KL (IH u), KL (EH i t wv)⟫_ℝ = ⟪KL (IH v), KL (eH j t ru)⟫_ℝ := by
  have hP := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
  calc ⟪KL (IH u), KL (EH i t wv)⟫_ℝ = ⟪KL (EH i t wv), KL (IH u)⟫_ℝ := real_inner_comm _ _
    _ = PP (EH i t wv) (JL (IH u)) := (hP _ _).symm
    _ = PP (IH wv) (JL (eH i t u)) := Cm.pivot i t ht wv u
    _ = PP (EH j t v) (JL (IH ru)) :=
      congrArg₂ (fun a b : Half => PP a (JL b)) hw hr.symm
    _ = PP (IH v) (JL (eH j t ru)) := Cm.pivot j t ht v ru
    _ = ⟪KL (IH v), KL (eH j t ru)⟫_ℝ := hP (IH v) (eH j t ru)

/-- GLOBAL pointwise physical adjoint for arbitrary finite test `F0` and input `G0`, each
satisfying the membership premise on its own support. -/
theorem pointwise_physical_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ =
      ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ := by
  by_cases hxF : x ∈ TS F0
  swap
  · have h1 : F0.val x = 0 := by
      first
        | exact image_eq_zero_of_notMem_tsupport hxF
        | exact image_eq_zero_of_nmem_tsupport hxF
    simp only [h1, revDouble_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p q F0 x hxF, map_zero, inner_zero_left]
  by_cases hxG : x ∈ TS G0
  swap
  · have h1 : G0.val x = 0 := by
      first
        | exact image_eq_zero_of_notMem_tsupport hxG
        | exact image_eq_zero_of_nmem_tsupport hxG
    simp only [h1, fwdDouble_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q G0 x hxG, map_zero, inner_zero_right]
  have ht := hTF x hxF
  have hFx : F0.val x = KL (IH (Uin F0 x)) :=
    (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD F0 x).symm
  have hGx : G0.val x = KL (IH (Uin G0 x)) :=
    (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD G0 x).symm
  have hrow (i j : Fin 3) :
      ⟪KL (IH (Uin F0 x)), KL (EH i ((Tq δr Ar p q) x) (VF δr Ar p q hreg δ0 W G0 j x))⟫_ℝ =
        ⟪KL (eH j ((Tq δr Ar p q) x) (VR hreg δ0 W δr Ar p q F0 i x)), KL (IH (Uin G0 x))⟫_ℝ :=
    (one_row_physical_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
      _ ht i j (Uin F0 x) (Uin G0 x) (VF δr Ar p q hreg δ0 W G0 j x)
      (VR hreg δ0 W δr Ar p q F0 i x)
      (fwdLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
        δr Ar p hδr hAr q G0 hTG j x)
      (ActualReverseEHigherLift.reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc
        hF hO hD τ0 hreg δ0 W δ Cm.rev δr Ar p q F0 hTF i x)).trans (real_inner_comm _ _)
  have hFwd := fwdDouble_eq g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p q G0 x
  have hRev : RD hreg δ0 W g2 δr Ar p q F0 x =
      (referenceRadius δr Ar p L x)^3 • (∑ i : Fin 3, ∑ j : Fin 3,
        referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
          eH j ((Tq δr Ar p q) x) (VR hreg δ0 W δr Ar p q F0 i x)) := by
    unfold revDoubleHalf
    rfl
  have hSum := inner_weighted_double_sum KL ((referenceRadius δr Ar p L x)^3)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
    (KL (IH (Uin F0 x))) (KL (IH (Uin G0 x)))
    (fun i j => EH i ((Tq δr Ar p q) x) (VF δr Ar p q hreg δ0 W G0 j x))
    (fun i j => eH j ((Tq δr Ar p q) x) (VR hreg δ0 W δr Ar p q F0 i x)) hrow
  have hLeft := congrArg₂ (fun a : SphereL2 => fun b : Half => ⟪a,KL b⟫_ℝ) hFx hFwd
  have hRight := congrArg₂ (fun a : Half => fun b : SphereL2 => ⟪KL a,b⟫_ℝ) hRev hGx
  exact hLeft.trans (hSum.trans hRight.symm)

/-- Integrated physical adjoint with the actual continuous density; integrability derived. -/
theorem integrated_physical_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ) ∧
    (∫ x, referenceDensityFamily g L (q,x) * ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (q,x) * ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ := by
  have hpt := pointwise_physical_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 G0 hTF hTG
  have hρ : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hFc : Continuous (fun x => F0.val x) := F0.property.1.continuous
  have hDc : Continuous (fun x => KL (FD δr Ar p q hreg δ0 W g2 G0 x)) :=
    (KL).continuous.comp (contDiff_fwdDouble g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q G0 hTG).continuous
  have hcont : Continuous (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) := hρ.mul (hFc.inner hDc)
  have hcs : HasCompactSupport (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) :=
    hasCompactSupport_of_eq_zero_off hO hD G0 _ (fun z hz => by
      simp [fwdDouble_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W g2 δr Ar p hδr hAr q G0 z hz])
  have hI : Integrable (fun x : R3 => referenceDensityFamily g L (q,x) *
      ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) :=
    hcont.integrable_of_hasCompactSupport hcs
  refine ⟨hI, ?_, ?_⟩
  · simpa only [hpt] using hI
  · simp only [hpt]

/-! ## 5. Exports -/

/-- Quadratic formation and adjoint contract on one `δ`, for one admissible `g2`. -/
def CommonQuadraticAdjointContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → 0 < Ar → ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 →
  ∀ F0 G0 : smoothCompactFiniteSphereCore hO hD,
    (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
    (∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      ContDiff ℝ ∞ (FD δr Ar p q hreg δ0 W g2 G0) ∧
      (∀ z ∉ TS G0, FD δr Ar p q hreg δ0 W g2 G0 z = 0) ∧
      HasCompactSupport (FD δr Ar p q hreg δ0 W g2 G0) ∧
      ContDiff ℝ ∞ (RD hreg δ0 W g2 δr Ar p q F0) ∧
      (∀ z ∉ TS F0, RD hreg δ0 W g2 δr Ar p q F0 z = 0) ∧
      HasCompactSupport (RD hreg δ0 W g2 δr Ar p q F0) ∧
      Continuous (fun x => KL (FD δr Ar p q hreg δ0 W g2 G0 x)) ∧
      HasCompactSupport (fun x => KL (FD δr Ar p q hreg δ0 W g2 G0 x)) ∧
      Continuous (fun x => KL (RD hreg δ0 W g2 δr Ar p q F0 x)) ∧
      HasCompactSupport (fun x => KL (RD hreg δ0 W g2 δr Ar p q F0 x)) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ‖KL (FD δr Ar p q hreg δ0 W g2 G0 x)‖ ^ 2) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ‖KL (RD hreg δ0 W g2 δr Ar p q F0 x)‖ ^ 2) ∧
      (∀ x : R3, ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ =
        ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ) ∧
      (∫ x, referenceDensityFamily g L (q,x) *
          ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) =
        ∫ x, referenceDensityFamily g L (q,x) *
          ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ

theorem commonQuadraticAdjointContract_of_room (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) :
    CommonQuadraticAdjointContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ g2 := by
  intro δr Ar p hδr hAr q _hq F0 G0 hTF hTG
  have hρ : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hFD := contDiff_fwdDouble g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q G0 hTG
  have hRD := contDiff_revDouble g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF
  have hFD0 := fwdDouble_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p hδr hAr q G0
  have hRD0 := revDouble_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p q F0
  have hKF : Continuous (fun x => KL (FD δr Ar p q hreg δ0 W g2 G0 x)) :=
    (KL).continuous.comp hFD.continuous
  have hKR : Continuous (fun x => KL (RD hreg δ0 W g2 δr Ar p q F0 x)) :=
    (KL).continuous.comp hRD.continuous
  have hKF0 : ∀ z ∉ TS G0, KL (FD δr Ar p q hreg δ0 W g2 G0 z) = 0 :=
    fun z hz => by rw [hFD0 z hz, map_zero]
  have hKR0 : ∀ z ∉ TS F0, KL (RD hreg δ0 W g2 δr Ar p q F0 z) = 0 :=
    fun z hz => by rw [hRD0 z hz, map_zero]
  have hNF : Integrable (fun x => referenceDensityFamily g L (q,x) *
      ‖KL (FD δr Ar p q hreg δ0 W g2 G0 x)‖ ^ 2) :=
    (hρ.mul (hKF.norm.pow 2)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_eq_zero_off hO hD G0 _ (fun z hz => by
        simp [hKF0 z hz]))
  have hNR : Integrable (fun x => referenceDensityFamily g L (q,x) *
      ‖KL (RD hreg δ0 W g2 δr Ar p q F0 x)‖ ^ 2) :=
    (hρ.mul (hKR.norm.pow 2)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_eq_zero_off hO hD F0 _ (fun z hz => by
        simp [hKR0 z hz]))
  have hInt := integrated_physical_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 G0 hTF hTG
  exact ⟨hFD, hFD0, hasCompactSupport_of_eq_zero_off hO hD G0 _ hFD0,
    hRD, hRD0, hasCompactSupport_of_eq_zero_off hO hD F0 _ hRD0,
    hKF, hasCompactSupport_of_eq_zero_off hO hD G0 _ hKF0,
    hKR, hasCompactSupport_of_eq_zero_off hO hD F0 _ hKR0,
    hNF, hNR,
    pointwise_physical_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 G0 hTF hTG,
    hInt.1, hInt.2.1, hInt.2.2⟩

/-- ANY retained W: `δ` and all room facts are chosen BEFORE every `g2`, profile, `F0`, `G0`. -/
theorem exists_retained_common_quadratic_adjoint (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, CRoom hreg δ0 W δ ∧
      CommonFirstWordLiftContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
        CommonQuadraticAdjointContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          hreg δ0 W δ g2 := by
  obtain ⟨δ, Cm⟩ := exists_common_first_word_room g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg hKernel δ0 hδ0 W
  exact ⟨δ, Cm,
    commonFirstWordLiftContract_of_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm,
    fun g2 hg2 => commonQuadraticAdjointContract_of_room g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 hg2⟩

/-- Ordinary actual packet: `δ0, W` selected exactly ONCE, then the retained producer. -/
theorem exists_actual_common_quadratic_adjoint (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ ρ ∧ ∃ W : CoeffRoom δ0, ∃ δ : ℝ, CRoom hreg δ0 W δ ∧
      CommonFirstWordLiftContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
        CommonQuadraticAdjointContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          hreg δ0 W δ g2 := by
  obtain ⟨δ0, hδ0, hδ0ρ, _hRoom, W, _⟩ :=
    exists_commonRoom_actual_fullE_ordinary_endpoints g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg
  obtain ⟨δ, Cm, hLift, hQuad⟩ := exists_retained_common_quadratic_adjoint g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  exact ⟨δ0, hδ0, hδ0ρ, W, δ, Cm, hLift, hQuad⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCommonFirstWordQuadraticAdjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCommonFirstWordQuadraticAdjoint.exists_actual_common_quadratic_adjoint
