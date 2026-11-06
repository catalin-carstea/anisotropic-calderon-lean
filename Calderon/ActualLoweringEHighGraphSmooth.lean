import Calderon.ActualLoweringEProductGraphs

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

private lemma retainedNative_contDiff (δ0 : ℝ) (W : CoeffRoom δ0) (c : RetainedCoefficient) :
    ContDiff ℝ ∞ (fun t => NH (QW δ0 W c t)) ∧
    ContDiff ℝ ∞ (fun t => NL (smoothMultiplierLowerJets (QW δ0 W c t))) := by
  cases c with
  | inl i =>
    constructor
    · simpa only [retainedJets, ActualPiJacobiRadialGainedRows.piJets] using
        contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
          (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i)
    · simpa only [retainedJets, ActualPiJacobiRadialGainedRows.piJets, smoothMultiplierLowerJets_commonSupport] using
        contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
          (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i)
  | inr im =>
    have hH := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (W.jacobiScalar im.1 im.2) (W.jacobiSmooth im.1 im.2) (W.jacobiSupport im.1 im.2)
      (W.jacobiCompact im.1 im.2) (W.jacobiZero im.1 im.2)
    have hL : ContDiff ℝ ∞ (fun p : Pphys => NL (smoothMultiplierLowerJets
        (jacobiJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W im.1 im.2 p))) := by
      simpa only [jacobiJets, smoothMultiplierLowerJets_commonSupport] using
        contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
          (W.jacobiScalar im.1 im.2) (W.jacobiSmooth im.1 im.2) (W.jacobiSupport im.1 im.2)
          (W.jacobiCompact im.1 im.2) (W.jacobiZero im.1 im.2)
    constructor
    · simpa only [retainedJets, jacobiJets, Function.comp_def] using hH.comp contDiff_fst
    · simpa only [retainedJets, Function.comp_def] using hL.comp contDiff_fst

private lemma zeroFamilies_contDiffOn (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0) (j : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : Tpar => ZH j t.1) (ParamRoom δ) ∧
    ContDiffOn ℝ ∞ (fun t : Tpar => ZL j t.1) (ParamRoom δ) ∧
    ContDiffOn ℝ ∞ (fun t : Tpar => zH j t.1) (ParamRoom δ) ∧
    ContDiffOn ℝ ∞ (fun t : Tpar => zL j t.1) (ParamRoom δ) := by
  have hNH (m : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar => NH (NJ3 j m t.1)) (ParamRoom δ) := by
    have h := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (W.jacobiScalar j m) (W.jacobiSmooth j m) (W.jacobiSupport j m) (W.jacobiCompact j m) (W.jacobiZero j m)
    intro t ht
    exact ((h.contDiffAt.congr_of_eventuallyEq
      ((W.jacobiGerm j m t.1 (hSub ht.1)).mono (fun z hz => hz.1.symm))).comp
      (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  have hNL (m : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar => NL (NJ2 j m t.1)) (ParamRoom δ) := by
    have h : ContDiff ℝ ∞ (fun p : Pphys => NL (smoothMultiplierLowerJets
        (jacobiJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j m p))) := by
      simpa only [jacobiJets, smoothMultiplierLowerJets_commonSupport] using
        contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
          (W.jacobiScalar j m) (W.jacobiSmooth j m) (W.jacobiSupport j m) (W.jacobiCompact j m) (W.jacobiZero j m)
    intro t ht
    exact ((h.contDiffAt.congr_of_eventuallyEq
      ((W.jacobiGerm j m t.1 (hSub ht.1)).mono (fun z hz => hz.2.1.symm))).comp
      (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  have hProj : ContDiff ℝ ∞ (fun t : Tpar => (t.1.1,t.1.2.1)) := contDiff_fst.fst.prodMk contDiff_fst.snd.fst
  have hDr (s : ℝ) := ((contDiff_reference_sphereSobolevRadialDriftAdjointL g hg L hF hO hD s).comp hProj).contDiffOn (s := ParamRoom δ)
  have hdr (s : ℝ) := ((contDiff_reference_sphereSobolevRadialDriftL g hg L hF hO hD s).comp hProj).contDiffOn (s := ParamRoom δ)
  have hr : ContDiffOn ℝ ∞ (fun t : Tpar => t.1.2.2) (ParamRoom δ) := contDiff_fst.snd.snd.contDiffOn
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold zeroCorrectionHigh
    exact hr.smul (ContDiffOn.sum (fun m _ => (hDr (3/2 : ℝ)).clm_comp (contDiffOn_const.clm_comp (hNH m))))
  · unfold zeroCorrectionHalf
    exact hr.smul (ContDiffOn.sum (fun m _ => (hDr (1/2 : ℝ)).clm_comp (contDiffOn_const.clm_comp (hNL m))))
  · unfold zeroReverseHigh
    exact hr.smul (ContDiffOn.sum (fun m _ => (hNH m).clm_comp (contDiffOn_const.clm_comp (hdr (3/2 : ℝ)))))
  · unfold zeroReverseHalf
    exact hr.smul (ContDiffOn.sum (fun m _ => (hNL m).clm_comp (contDiffOn_const.clm_comp (hdr (1/2 : ℝ)))))

theorem lowering_E_both_smooth
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (G : Fin 3 → Pphys → Half →L[ℝ] Half) (δ : ℝ)
    (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0)
    (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (hU : ∀ V : Generator, ∀ c : RetainedCoefficient,
      ContDiffOn ℝ ∞ (GH δ0 W V c) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (GL δ0 W V c) (ParamRoom δ))
    (hRad : ∀ i : Fin 3, ContDiffOn ℝ ∞ (CaT hreg G i) (commonRoom y0 ρ δ) ∧
      ContDiffOn ℝ ∞ (CAS hreg i) (commonRoom y0 ρ δ))
    (i j : Fin 3) :
    ContDiffOn ℝ ∞ (LF hreg δ0 W G i j) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (RF hreg δ0 W i j) (ParamRoom δ) := by
  have hProj : MapsTo (Prod.fst : Tpar → Pphys) (ParamRoom δ) (commonRoom y0 ρ δ) := fun t ht => ht.1
  have hCaT := (hRad i).1.comp contDiffOn_fst hProj
  have hCAS := (hRad i).2.comp contDiffOn_fst hProj
  have hQ (c : RetainedCoefficient) := retainedNative_contDiff
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W c
  have hQH (c : RetainedCoefficient) : ContDiffOn ℝ ∞ (fun t => NH (QW δ0 W c t)) (ParamRoom δ) :=
    (hQ c).1.contDiffOn
  have hQL (c : RetainedCoefficient) : ContDiffOn ℝ ∞ (fun t => NL (smoothMultiplierLowerJets (QW δ0 W c t))) (ParamRoom δ) :=
    (hQ c).2.contDiffOn
  have hLP (c : RetainedCoefficient) : ContDiffOn ℝ ∞ (LP δ0 W i c) (ParamRoom δ) := by
    unfold loweringMultiplierHigh
    exact (ContDiffOn.sum (fun k _ => contDiffOn_const.clm_comp (hU (Sum.inl (k,i)) c).1)).add
      (contDiffOn_const.clm_comp (hU (Sum.inr ()) c).1)
  have hRP (c : RetainedCoefficient) : ContDiffOn ℝ ∞ (RP δ0 W i c) (ParamRoom δ) := by
    unfold raisingMultiplierHalf
    exact (ContDiffOn.sum (fun k _ => (hU (Sum.inl (k,i)) c).2.clm_comp contDiffOn_const)).sub
      ((hU (Sum.inr ()) c).2.clm_comp contDiffOn_const)
  have hZ := zeroFamilies_contDiffOn
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W δ hSub j
  have hRem (t : Tpar) (ht : t ∈ ParamRoom δ) := contDiffAt_actualAngularRadialRemainder_families_of_segment
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1
    (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1)
  have hTh : ContDiffOn ℝ ∞ (fun t : Tpar => Th t.1) (ParamRoom δ) := fun t ht =>
    ((hRem t ht).1.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  have hSh : ContDiffOn ℝ ∞ (fun t : Tpar => Sh t.1) (ParamRoom δ) := fun t ht =>
    ((hRem t ht).2.2.1.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  have hL0 : ContDiffOn ℝ ∞
      (fun t : Tpar => (CaT hreg G i t.1).comp (NH (QW δ0 W (Sum.inl j) t))) (ParamRoom δ) :=
    hCaT.clm_comp (hQH (Sum.inl j))
  have hL1 : ContDiffOn ℝ ∞
      (fun t : Tpar => (Th t.1).comp (LP δ0 W i (Sum.inl j) t)) (ParamRoom δ) :=
    hTh.clm_comp (hLP (Sum.inl j))
  have hL2 : ContDiffOn ℝ ∞
      (fun t : Tpar => ∑ m : Fin 3,
        ((CH i m).comp (NH (QW δ0 W (Sum.inr (j,m)) t)) +
          (AH m).comp (LP δ0 W i (Sum.inr (j,m)) t))) (ParamRoom δ) :=
    ContDiffOn.sum (fun m _ => (contDiffOn_const.clm_comp (hQH (Sum.inr (j,m)))).add
      (contDiffOn_const.clm_comp (hLP (Sum.inr (j,m)))))
  have hL3 : ContDiffOn ℝ ∞ (fun t : Tpar => (aH i).comp (ZH j t.1)) (ParamRoom δ) :=
    contDiffOn_const.clm_comp hZ.1
  have hL4 : ContDiffOn ℝ ∞ (fun t : Tpar => (ZL j t.1).comp (aH i)) (ParamRoom δ) :=
    hZ.2.1.clm_comp contDiffOn_const
  have hR0 : ContDiffOn ℝ ∞
      (fun t : Tpar => (RP δ0 W i (Sum.inl j) t).comp (Sh t.1)) (ParamRoom δ) :=
    (hRP (Sum.inl j)).clm_comp hSh
  have hR1 : ContDiffOn ℝ ∞
      (fun t : Tpar => (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t))).comp
        (-CAS hreg i t.1)) (ParamRoom δ) :=
    (hQL (Sum.inl j)).clm_comp hCAS.neg
  have hR2 : ContDiffOn ℝ ∞
      (fun t : Tpar => ∑ m : Fin 3,
        ((RP δ0 W i (Sum.inr (j,m)) t).comp (aH m) +
          (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t))).comp (CH m i))) (ParamRoom δ) :=
    ContDiffOn.sum (fun m _ => ((hRP (Sum.inr (j,m))).clm_comp contDiffOn_const).add
      ((hQL (Sum.inr (j,m))).clm_comp contDiffOn_const))
  have hR3 : ContDiffOn ℝ ∞ (fun t : Tpar => (zL j t.1).comp (AH i)) (ParamRoom δ) :=
    hZ.2.2.2.clm_comp contDiffOn_const
  have hR4 : ContDiffOn ℝ ∞ (fun t : Tpar => (AH i).comp (zH j t.1)) (ParamRoom δ) :=
    contDiffOn_const.clm_comp hZ.2.2.1
  constructor
  · change ContDiffOn ℝ ∞ (fun t : Tpar => LF hreg δ0 W G i j t) (ParamRoom δ)
    unfold loweringEHigh
    exact (((hL0.add hL1).add hL2).add hL3).sub hL4
  · change ContDiffOn ℝ ∞ (fun t : Tpar => RF hreg δ0 W i j t) (ParamRoom δ)
    unfold reverseERaisingHigh
    exact (((hR0.add hR1).add hR2).add hR3).sub hR4

theorem lowering_E_paired_adjunction_at
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (G : Fin 3 → Pphys → Half →L[ℝ] Half) (i j : Fin 3) (t : Tpar)
    (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hL : ∀ u, JL (LF hreg δ0 W G i j t u) = aL i (EH j t u) - EL j t (aH i u))
    (hR : ∀ u, JL (RF hreg δ0 W i j t u) = eL j t (AH i u) - AL i (eH j t u))
    (u v : Hi) :
    PP (IH v) (JL (LF hreg δ0 W G i j t u)) =
      PP (IH u) (JL (RF hreg δ0 W i j t v)) := by
  have hp := (W.piGerm j t ht).self_of_nhds
  let Q := ActualPiJacobiRadialGainedRows.piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t
  have hEC (z : Hi) := canonicalHigh_low_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg j t hSeg Q hp.1 hp.2.1 z
  have heC (z : Hi) : JL (eH j t z) = eL j t (IH z) := by
    simpa only [reverseEHigh, reverseELow] using explicit_ordered_reverse_high_low_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t hSeg Q hp.2.1 hp.2.2 z
  have hP (x y : Half) : PP x (EL j t y) = PP y (eL j t x) := by
    simpa only [reverseELow] using canonicalLow_explicit_ordered_reverse_pairing
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t hSeg Q hp.2.1 hp.2.2 x y
  have hForward (z : Hi) (x : Half) : PP (IH z) (EL j t x) = PP x (JL (eH j t z)) :=
    (hP (IH z) x).trans (congrArg (PP x) (heC z).symm)
  have hReverse (z : Hi) (x : Half) : PP (IH z) (eL j t x) = PP x (JL (EH j t z)) :=
    (hP x (IH z)).symm.trans (congrArg (PP x) (hEC z).symm)
  have h1 : PP (IH v) (aL i (EH j t u)) = PP (IH u) (eL j t (AH i v)) :=
    (v017_aA1 hF hO hD i v (EH j t u)).trans
      ((v016_pairing_inclusion_symm (EH j t u) (AH i v)).trans (hReverse u (AH i v)).symm)
  have h2 : PP (IH v) (EL j t (aH i u)) = PP (IH u) (AL i (eH j t v)) :=
    (hForward v (aH i u)).trans (v017_aA2 hF hO hD i u (eH j t v))
  have hleft := (congrArg (fun n : Neg => PP (IH v) n) (hL u)).trans (v016_pairing_sub_right (IH v) _ _)
  have hright := (congrArg (fun n : Neg => PP (IH u) n) (hR v)).trans (v016_pairing_sub_right (IH u) _ _)
  exact hleft.trans ((congrArg₂ (fun x y : ℝ => x-y) h1 h2).trans hright.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
