import Calderon.ActualGeneratorEndpointSmoothGerms
import Calderon.ActualGeneratorEHighGainedGraph

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEHighSmoothGerms
open ActualGeneratorEHighGainedGraph ActualGeneratorEndpointSmoothGerms
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GH" => retainedGeneratorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "CGE" => generatorEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

private lemma retainedNative_contDiff (δ0 : ℝ) (W : CoeffRoom δ0) (c : RetainedCoefficient) :
    ContDiff ℝ ∞ (fun t => NH (QW δ0 W c t)) ∧
    ContDiff ℝ ∞ (fun t => NL (smoothMultiplierLowerJets (QW δ0 W c t))) := by
  cases c with
  | inl i =>
    refine ⟨contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i),?_⟩
    simpa only [retainedJets,piJets,smoothMultiplierLowerJets_commonSupport] using
      contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
        (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i)
  | inr im =>
    have hH := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (W.jacobiScalar im.1 im.2) (W.jacobiSmooth im.1 im.2) (W.jacobiSupport im.1 im.2)
      (W.jacobiCompact im.1 im.2) (W.jacobiZero im.1 im.2)
    have hL : ContDiff ℝ ∞ (fun p : Pphys => NL (smoothMultiplierLowerJets
        (jacobiJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W im.1 im.2 p))) := by
      simpa only [jacobiJets,smoothMultiplierLowerJets_commonSupport] using
        contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
          (W.jacobiScalar im.1 im.2) (W.jacobiSmooth im.1 im.2) (W.jacobiSupport im.1 im.2)
          (W.jacobiCompact im.1 im.2) (W.jacobiZero im.1 im.2)
    exact ⟨hH.comp contDiff_fst,hL.comp contDiff_fst⟩

private lemma zeroForward_contDiffAt (δ0 : ℝ) (W : CoeffRoom δ0) (j : Fin 3)
    (t : Tpar) (ht : t ∈ ParamRoom δ0) :
    ContDiffAt ℝ ∞ (fun z : Tpar => ZH j z.1) t ∧
      ContDiffAt ℝ ∞ (fun z : Tpar => ZL j z.1) t := by
  have hNH (m : Fin 3) : ContDiffAt ℝ ∞ (fun z : Tpar => NH (NJ3 j m z.1)) t := by
    have h := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (W.jacobiScalar j m) (W.jacobiSmooth j m) (W.jacobiSupport j m)
      (W.jacobiCompact j m) (W.jacobiZero j m)
    exact (h.contDiffAt.congr_of_eventuallyEq
      ((W.jacobiGerm j m t.1 ht.1).mono (fun z hz => hz.1.symm))).comp
        (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst
  have hNL (m : Fin 3) : ContDiffAt ℝ ∞ (fun z : Tpar => NL (NJ2 j m z.1)) t := by
    have h : ContDiff ℝ ∞ (fun p : Pphys => NL (smoothMultiplierLowerJets
        (jacobiJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j m p))) := by
      simpa only [jacobiJets,smoothMultiplierLowerJets_commonSupport] using
        contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
          (W.jacobiScalar j m) (W.jacobiSmooth j m) (W.jacobiSupport j m)
          (W.jacobiCompact j m) (W.jacobiZero j m)
    exact (h.contDiffAt.congr_of_eventuallyEq
      ((W.jacobiGerm j m t.1 ht.1).mono (fun z hz => hz.2.1.symm))).comp
        (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst
  have hProj : ContDiff ℝ ∞ (fun z : Tpar => (z.1.1,z.1.2.1)) :=
    contDiff_fst.fst.prodMk contDiff_fst.snd.fst
  have hDr (s : ℝ) : ContDiffAt ℝ ∞ (fun z : Tpar =>
      sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L z.1.1 z.1.2.1)) t :=
    ((contDiff_reference_sphereSobolevRadialDriftAdjointL g hg L hF hO hD s).comp hProj).contDiffAt
  have hr : ContDiffAt ℝ ∞ (fun z : Tpar => z.1.2.2) t := contDiffAt_fst.snd.snd
  constructor
  · exact hr.smul (ContDiffAt.sum (fun m _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNH m))))
  · exact hr.smul (ContDiffAt.sum (fun m _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNL m))))

/-- The actual full generator/E high family has neighborhood smoothness on one room. -/
private def actualGeneratorEHighGermFoldedContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ V : Generator, ∀ j : Fin 3, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (CGE hreg δ0 W V j) t
attribute [local irreducible] actualGeneratorEHighGermFoldedContract
private theorem actualGeneratorEHighGermFoldedContract_proof
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    actualGeneratorEHighGermFoldedContract hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg δ0 W := by
  obtain ⟨dU,hdU,hdU0,hdUρ,hUAt⟩ :=
    exists_commonRoom_retained_generator_multiplier_contDiffAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 hδ0 W
  obtain ⟨dR,hdR,_hdRρ,hRoomR,_hRS,_hRG,_hRC⟩ :=
    exists_commonRoom_actual_generator_radial_high_gains
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let δ := min dU dR
  have hδ : 0 < δ := lt_min hdU hdR
  have hSubU := commonRoom_mono y0 ρ (show δ ≤ dU from min_le_left _ _)
  have hSubR := commonRoom_mono y0 ρ (show δ ≤ dR from min_le_right _ _)
  have hSub0 := commonRoom_mono y0 ρ ((show δ ≤ dU from min_le_left _ _).trans hdU0)
  unfold actualGeneratorEHighGermFoldedContract
  refine ⟨δ,hδ,(min_le_left _ _).trans hdU0,(min_le_left _ _).trans hdUρ,?_⟩
  intro V j t ht
  have htU : t ∈ ParamRoom dU := ⟨hSubU ht.1,ht.2⟩
  have ht0 : t ∈ ParamRoom δ0 := ⟨hSub0 ht.1,ht.2⟩
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData hRoomR t.1 (hSubR ht.1)
  have hCT := (generatorRadialHigh_contDiffAt g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 hreg V t.1 hSeg).1.comp
      (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst
  have hTh := (contDiffAt_actualAngularRadialRemainder_families_of_segment
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg).1.comp
      (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst
  have hN (c : RetainedCoefficient) := (retainedNative_contDiff
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δ0 W c).1.contDiffAt (x := t)
  have hG (c : RetainedCoefficient) := (hUAt V c t htU).1
  have hZ := zeroForward_contDiffAt hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δ0 W j t ht0
  have hR := (hCT.clm_comp (hN (Sum.inl j))).add (hTh.clm_comp (hG (Sum.inl j)))
  have hA : ContDiffAt ℝ ∞ (fun z : Tpar => ∑ m : Fin 3, (
      (generatorRaisingHigh hF hO hD V m).comp (NH (QW δ0 W (Sum.inr (j,m)) z)) +
      (raisingHigh hF hO hD m).comp (GH δ0 W V (Sum.inr (j,m)) z))) t :=
    ContDiffAt.sum (fun m _ => (contDiffAt_const.clm_comp (hN (Sum.inr (j,m)))).add
      (contDiffAt_const.clm_comp (hG (Sum.inr (j,m)))))
  have hZHigh : ContDiffAt ℝ ∞ (fun z : Tpar => (generatorHigh V).comp (ZH j z.1)) t :=
    contDiffAt_const.clm_comp hZ.1
  have hZLow : ContDiffAt ℝ ∞ (fun z : Tpar => (ZL j z.1).comp (generatorHigh V)) t :=
    hZ.2.clm_comp contDiffAt_const
  have hFinal := ((hR.add hA).add hZHigh).sub hZLow
  change ContDiffAt ℝ ∞ (fun z : Tpar => CGE hreg δ0 W V j z) t
  simpa only [generatorEHigh,Function.comp_def] using hFinal


theorem exists_commonRoom_actual_generator_E_high_contDiffAt
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ V : Generator, ∀ j : Fin 3, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (CGE hreg δ0 W V j) t := by
  simpa only [actualGeneratorEHighGermFoldedContract] using
    (actualGeneratorEHighGermFoldedContract_proof hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg δ0 hδ0 W)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEHighSmoothGerms
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEHighSmoothGerms.exists_commonRoom_actual_generator_E_high_contDiffAt
