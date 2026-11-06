import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualFullEZeroRowsSmoothGerms
import Calderon.ActualGeneratorEndpointSmoothGerms
import Calderon.ActualHigherSFormation

/-! Actual genuine reverse-E (public `reverseEHigh`, `reverseELow`, `generatorReverseEHigh`):
ambient C^∞ germs at every closed parameter-room point on ANY retained W, the partner graph
and high/low compatibility on the SAME W, and the explicit global finite-input Hi lift
`Vrev_j = BesselOrder Half Hi (DGE(B,j) u + eH_j uB + eH_j u)` with global inclusion,
global C^∞ and compact support. Physical degree B(k)=k including 0. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseEHigherLift
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
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
local notation "UL" => retainedGeneratorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CS" => generatorSharpRadialHigh g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "Sh" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sl" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DGE" => generatorReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DH" => pairedRightHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "UBin" => ActualHigherSFormation.higherSDegreeInput hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-! ## 1. Ambient C^∞ germs of the genuine reverse maps at every closed-room point -/

/-- Ambient germs of `eH_j`, `eL_j` and `DGE(V,j)` at EVERY point of the closed room
`ParamRoom δ` (boundary included), from neighborhood W germs, common-support native
multipliers, segment remainder germs, the actual radial generator germ and the given
ambient retained UL germs (discharged by the producer in §2). -/
theorem reverseE_ambient_contDiffAt (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0) (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (hUL : ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
      ContDiffAt ℝ ∞ (UL δ0 W V c) t)
    (j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
    ContDiffAt ℝ ∞ (eH j) t ∧ ContDiffAt ℝ ∞ (eL j) t ∧
      ∀ V : Generator, ContDiffAt ℝ ∞ (DGE hreg δ0 W V j) t := by
  have ht0 : t ∈ ParamRoom δ0 := ⟨hSub ht.1, ht.2⟩
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
  have hRem := contDiffAt_actualAngularRadialRemainder_families_of_segment
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg
  have hSh : ContDiffAt ℝ ∞ (fun s : Tpar => Sh s.1) t :=
    hRem.2.2.1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  have hSl : ContDiffAt ℝ ∞ (fun s : Tpar => Sl s.1) t :=
    hRem.2.2.2.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  -- Pi germs from the actual neighborhood W.piGerm
  have hPi := ActualFullEZeroRowsSmoothGerms.commonSupport_native_contDiffAt hcalc hF hO hD τ0
    (W.piScalar j) (W.piSmooth j) W.piSupport W.piCompact (W.piZero j) t
  have hPiGerm := W.piGerm j t ht0
  have hPiL : ContDiffAt ℝ ∞ (PiL j) t :=
    hPi.2.1.congr_of_eventuallyEq (hPiGerm.mono (fun z hz => hz.2.1.symm))
  have hPiN : ContDiffAt ℝ ∞ (PiN j) t :=
    hPi.2.2.congr_of_eventuallyEq (hPiGerm.mono (fun z hz => hz.2.2.symm))
  -- Jacobi germs from the actual neighborhood W.jacobiGerm
  have hNp (i m : Fin 3) :
      ContDiffAt ℝ ∞ (fun z : Pphys => NH (NJ3 i m z)) t.1 ∧
      ContDiffAt ℝ ∞ (fun z : Pphys => NL (NJ2 i m z)) t.1 ∧
      ContDiffAt ℝ ∞ (fun z : Pphys => NN (NJ2 i m z)) t.1 := by
    have hs := ActualFullEZeroRowsSmoothGerms.commonSupport_native_contDiffAt hcalc hF hO hD τ0
      (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m) (W.jacobiCompact i m)
      (W.jacobiZero i m) t.1
    have hgerm := W.jacobiGerm i m t.1 ht0.1
    exact ⟨hs.1.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.1.symm)),
      hs.2.1.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.1.symm)),
      hs.2.2.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.2.symm))⟩
  have hNH (i m : Fin 3) : ContDiffAt ℝ ∞ (fun s : Tpar => NH (NJ3 i m s.1)) t :=
    (hNp i m).1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  have hNL (i m : Fin 3) : ContDiffAt ℝ ∞ (fun s : Tpar => NL (NJ2 i m s.1)) t :=
    (hNp i m).2.1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  have hNN (i m : Fin 3) : ContDiffAt ℝ ∞ (fun s : Tpar => NN (NJ2 i m s.1)) t :=
    (hNp i m).2.2.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  -- native zero reverse rows
  have hProj : ContDiff ℝ ∞ (fun z : Tpar => (z.1.1,z.1.2.1)) :=
    contDiff_fst.fst.prodMk contDiff_fst.snd.fst
  have hdr (s : ℝ) : ContDiffAt ℝ ∞ (fun z : Tpar =>
      sphereSobolevRadialDriftL hF hO hD s (referenceCenterDrift g L z.1.1 z.1.2.1)) t :=
    ((contDiff_reference_sphereSobolevRadialDriftL g hg L hF hO hD s).comp hProj).contDiffAt
  have hr : ContDiffAt ℝ ∞ (fun z : Tpar => z.1.2.2) t := contDiffAt_fst.snd.snd
  have hzH : ContDiffAt ℝ ∞ (fun s : Tpar => zH j s.1) t :=
    hr.smul (ContDiffAt.sum (fun m _ => (hNH j m).clm_comp (contDiffAt_const.clm_comp (hdr _))))
  have hzL : ContDiffAt ℝ ∞ (fun s : Tpar => zL j s.1) t :=
    hr.smul (ContDiffAt.sum (fun m _ => (hNL j m).clm_comp (contDiffAt_const.clm_comp (hdr _))))
  -- common-support retained native lower multipliers
  have hQL (c : RetainedCoefficient) :
      ContDiffAt ℝ ∞ (fun s : Tpar => NL (smoothMultiplierLowerJets (QW δ0 W c s))) t := by
    cases c with
    | inl i =>
      exact (ActualFullEZeroRowsSmoothGerms.commonSupport_native_contDiffAt hcalc hF hO hD τ0
        (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i) t).2.1
    | inr im =>
      exact (ActualFullEZeroRowsSmoothGerms.commonSupport_native_contDiffAt hcalc hF hO hD τ0
        (W.jacobiScalar im.1 im.2) (W.jacobiSmooth im.1 im.2) (W.jacobiSupport im.1 im.2)
        (W.jacobiCompact im.1 im.2) (W.jacobiZero im.1 im.2) t.1).2.1.comp
          (f := fun z : Tpar => z.1) t contDiffAt_fst
  refine ⟨?_,?_,?_⟩
  · exact ((hPiL.clm_comp hSh).add
      (ContDiffAt.sum (fun m _ => (hNL j m).clm_comp contDiffAt_const))).add
        (contDiffAt_const.clm_comp hzH)
  · exact ((hPiN.clm_comp hSl).add
      (ContDiffAt.sum (fun m _ => (hNN j m).clm_comp contDiffAt_const))).add
        (contDiffAt_const.clm_comp hzL)
  · intro V
    have hCS : ContDiffAt ℝ ∞ (fun s : Tpar => CS hreg V s.1) t :=
      (generatorRadialHigh_contDiffAt g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg V t.1
        hSeg).2.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
    exact (((((hUL V (Sum.inl j) t ht).clm_comp hSh).add ((hQL (Sum.inl j)).clm_comp hCS)).add
      (ContDiffAt.sum (fun m _ => ((hUL V (Sum.inr (j,m)) t ht).clm_comp contDiffAt_const).add
        ((hQL (Sum.inr (j,m))).clm_comp contDiffAt_const)))).add
      (contDiffAt_const.clm_comp hzH)).sub (hzL.clm_comp contDiffAt_const)

/-! ## 2. Graph, compatibility and the retained-W packet -/

/-- Typed additive negation of the public partner graph (`DH = -DGE`). -/
theorem reverseE_graph_of_partner (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (V : Generator) (j : Fin 3) (t : Tpar) (u : Hi)
    (hP : JL (DH hreg δ0 W V j t u) = eL j t (generatorHigh V u) - generatorLow V (eH j t u)) :
    JL (DGE hreg δ0 W V j t u) = generatorLow V (eH j t u) - eL j t (generatorHigh V u) := by
  have h1 : JL (DGE hreg δ0 W V j t u) = -JL (DH hreg δ0 W V j t u) := by
    simp only [pairedRightHigh, ContinuousLinearMap.neg_apply, map_neg, neg_neg]
  have h2 : -JL (DH hreg δ0 W V j t u) = generatorLow V (eH j t u) - eL j t (generatorHigh V u) :=
    (congrArg (fun x : Neg => -x) hP).trans (neg_sub _ _)
  exact h1.trans h2

/-- `J (eH_j u) = eL_j (IH u)` from the actual W Pi germ and the invertibility segment. -/
theorem reverseE_high_low_compat (δ0 : ℝ) (W : CoeffRoom δ0) (j : Fin 3) (t : Tpar)
    (ht0 : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω) (u : Hi) :
    JL (eH j t u) = eL j t (IH u) := by
  have hp := (W.piGerm j t ht0).self_of_nhds
  let Q := piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t
  simpa only [reverseEHigh, reverseELow] using explicit_ordered_reverse_high_low_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t hSeg Q hp.2.1 hp.2.2 u

/-- One retained-W packet of actual discharged facts on a single closed room. -/
structure ReverseERoom (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) : Prop where
  pos : 0 < δ
  le0 : δ ≤ δ0
  leρ : δ ≤ ρ
  room : commonRoom y0 ρ δ ⊆ Ω
  germHigh : ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (eH j) t
  germLow : ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (eL j) t
  germGen : ∀ V : Generator, ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (DGE hreg δ0 W V j) t
  graph : ∀ V : Generator, ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
    JL (DGE hreg δ0 W V j t u) = generatorLow V (eH j t u) - eL j t (generatorHigh V u)
  compat : ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (eH j t u) = eL j t (IH u)
local notation "RevRoom" => ReverseERoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Producer on ANY retained W (no new W is chosen). -/
theorem exists_retained_reverseE_room (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, RevRoom hreg δ0 W δ := by
  obtain ⟨dP,hdP,hdP0,hdPρ,hRoomP,⟨P⟩⟩ := exists_retained_generator_paired_endpoints
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  obtain ⟨dU,hdU,_hdU0,_hdUρ,hUAt⟩ :=
    ActualGeneratorEndpointSmoothGerms.exists_commonRoom_retained_generator_multiplier_contDiffAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 hδ0 W
  have hleP : min dP dU ≤ dP := min_le_left _ _
  have hleU : min dP dU ≤ dU := min_le_right _ _
  have hSubP := commonRoom_mono y0 ρ hleP
  have hSubU := commonRoom_mono y0 ρ hleU
  have hSub0 : commonRoom y0 ρ (min dP dU) ⊆ commonRoom y0 ρ δ0 :=
    hSubP.trans (commonRoom_mono y0 ρ hdP0)
  have hRoom : commonRoom y0 ρ (min dP dU) ⊆ Ω := hSubP.trans hRoomP
  have hUL : ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom (min dP dU),
      ContDiffAt ℝ ∞ (UL δ0 W V c) t :=
    fun V c t ht => (hUAt V c t ⟨hSubU ht.1, ht.2⟩).2
  have hGerm (j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom (min dP dU)) :=
    reverseE_ambient_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W (min dP dU) hSub0 hRoom hUL j t ht
  exact ⟨min dP dU, {
    pos := lt_min hdP hdU
    le0 := hleP.trans hdP0
    leρ := hleP.trans hdPρ
    room := hRoom
    germHigh := fun j t ht => (hGerm j t ht).1
    germLow := fun j t ht => (hGerm j t ht).2.1
    germGen := fun V j t ht => (hGerm j t ht).2.2 V
    graph := fun V j t ht u => reverseE_graph_of_partner g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W V j t u (P.partnerGraph V j t ⟨hSubP ht.1, ht.2⟩ u)
    compat := fun j t ht u => reverseE_high_low_compat g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 δ0 W j t ⟨hSub0 ht.1, ht.2⟩
      (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1) u }⟩

/-! ## 3. The explicit global finite-input Hi lift -/

/-- `Vrev_j(x) = BesselOrder Half Hi (DGE(B,j,T x) U(x) + eH_j(T x) UB(x) + eH_j(T x) U(x))`
on ALL of R3, with `B = Sum.inr ()` the physical degree. -/
def reverseEHigherLift (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (x : R3) : Hi :=
  sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)
    (DGE hreg δ0 W (Sum.inr ()) j ((Tq δr Ar p q) x) (Uin F0 x) +
      eH j ((Tq δr Ar p q) x) (UBin F0 x) + eH j ((Tq δr Ar p q) x) (Uin F0 x))
local notation "Vrev" => reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

lemma revInput_eq_zero (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3) (hz : z ∉ TS F0) :
    Uin F0 z = 0 :=
  ActualHigherSFormation.finiteCoreSobolevLift_eq_zero_of_eval hO hD (3/2 : ℝ) F0 z
    (ActualHigherSFormation.eval_eq_zero_of_notMem_tsupport hO hD F0 z hz)

lemma revDegreeInput_eq_zero (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3) (hz : z ∉ TS F0) :
    UBin F0 z = 0 := by
  have hU : finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 z = 0 := revInput_eq_zero hO hD F0 z hz
  have h1 := inclusion_finiteCoreSobolevLift_coreDegree hO hD F0 z
  have h2 := sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) (coreDegree hO hD F0) z
  have hB : (sphereSobolevShiftedDegreeL (3/2 : ℝ)
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 z) : Half) = 0 := by
    rw [hU, map_zero]
  exact ActualHigherSFormation.finiteCoreSobolevLift_eq_zero_of_eq_zero hO hD (3/2 : ℝ) (1/2 : ℝ) _ z
    (h2.symm.trans (h1.trans hB))

/-- Off the input support the lift vanishes (identical finite coordinates). -/
lemma reverseEHigherLift_eq_zero (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3)
    (z : R3) (hz : z ∉ TS F0) : Vrev hreg δ0 W δr Ar p q F0 j z = 0 := by
  have hU := revInput_eq_zero hO hD F0 z hz
  have hB := revDegreeInput_eq_zero hO hD F0 z hz
  simp only [reverseEHigherLift, hU, hB, map_zero, add_zero]

section Inclusion
attribute [local irreducible] reverseEHigh reverseELow generatorReverseEHigh sphereSobolevInclusionL

/-- Bessel mechanism at one point from the B graph and the compatibility there. -/
lemma reverseEHigherLift_inclusion_of_graph (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (j : Fin 3) (x : R3)
    (hGraph : ∀ v : Hi, JL (DGE hreg δ0 W (Sum.inr ()) j ((Tq δr Ar p q) x) v) =
      generatorLow (Sum.inr ()) (eH j ((Tq δr Ar p q) x) v) -
        eL j ((Tq δr Ar p q) x) (generatorHigh (Sum.inr ()) v))
    (hCompat : ∀ v : Hi, JL (eH j ((Tq δr Ar p q) x) v) = eL j ((Tq δr Ar p q) x) (IH v)) :
    IH (Vrev hreg δ0 W δr Ar p q F0 j x) = eH j ((Tq δr Ar p q) x) (Uin F0 x) := by
  have hG : JL (DGE hreg δ0 W (Sum.inr ()) j ((Tq δr Ar p q) x) (Uin F0 x)) =
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) (eH j ((Tq δr Ar p q) x) (Uin F0 x)) : Neg) -
        eL j ((Tq δr Ar p q) x) (sphereSobolevShiftedDegreeL (3/2 : ℝ) (Uin F0 x) : Half) :=
    hGraph (Uin F0 x)
  have hS := inclusion_finiteCoreSobolevLift_coreDegree hO hD F0 x
  have hB : eL j ((Tq δr Ar p q) x) (sphereSobolevShiftedDegreeL (3/2 : ℝ) (Uin F0 x) : Half) =
      JL (eH j ((Tq δr Ar p q) x) (UBin F0 x)) :=
    (congrArg (eL j ((Tq δr Ar p q) x)) hS.symm).trans (hCompat (UBin F0 x)).symm
  have hDeg : (sphereSobolevShiftedDegreeL (1/2 : ℝ) (eH j ((Tq δr Ar p q) x) (Uin F0 x)) : Neg) =
      JL (DGE hreg δ0 W (Sum.inr ()) j ((Tq δr Ar p q) x) (Uin F0 x) +
        eH j ((Tq δr Ar p q) x) (UBin F0 x)) := by
    have hCombined := (map_add JL
      (DGE hreg δ0 W (Sum.inr ()) j ((Tq δr Ar p q) x) (Uin F0 x))
      (eH j ((Tq δr Ar p q) x) (UBin F0 x))).trans
      (congrArg₂ (fun a b : Neg => a+b) hG hB.symm)
    exact (hCombined.trans (sub_add_cancel _ _)).symm
  exact inclusion_besselOrder_eq_of_half_degree_graph (eH j ((Tq δr Ar p q) x) (Uin F0 x))
    (DGE hreg δ0 W (Sum.inr ()) j ((Tq δr Ar p q) x) (Uin F0 x) +
      eH j ((Tq δr Ar p q) x) (UBin F0 x)) hDeg

end Inclusion

/-- GLOBAL inclusion `IH Vrev_j = eH_j(T x) U(x)` on all of R3, with only the
membership premise on the input support. -/
theorem reverseEHigherLift_inclusion (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (R : RevRoom hreg δ0 W δ) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (j : Fin 3) (x : R3) :
    IH (Vrev hreg δ0 W δr Ar p q F0 j x) = eH j ((Tq δr Ar p q) x) (Uin F0 x) := by
  by_cases hx : x ∈ TS F0
  · exact reverseEHigherLift_inclusion_of_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δr Ar p q F0 j x (R.graph (Sum.inr ()) j _ (hT x hx)) (R.compat j _ (hT x hx))
  · have h1 := reverseEHigherLift_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δr Ar p q F0 j x hx
    have h2 := revInput_eq_zero hO hD F0 x hx
    simp only [h1, h2, map_zero]

/-- Membership-only family glue: ambient germ at support points, locally zero off support. -/
lemma reverseE_family_apply (δr Ar : ℝ) (p : ℕ) (q : ℝ) (hTs : ContDiff ℝ ∞ (Tq δr Ar p q))
    (A : Tpar → Hi →L[ℝ] Half) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hA : ∀ x ∈ TS F0, ContDiffAt ℝ ∞ A ((Tq δr Ar p q) x))
    (Wf : R3 → Hi) (hW : ContDiff ℝ ∞ Wf) (hW0 : ∀ z ∉ TS F0, Wf z = 0) :
    ContDiff ℝ ∞ (fun z => A ((Tq δr Ar p q) z) (Wf z)) := by
  refine contDiff_iff_contDiffAt.2 (fun x => ?_)
  by_cases hx : x ∈ TS F0
  · exact ((hA x hx).comp (f := Tq δr Ar p q) x hTs.contDiffAt).clm_apply hW.contDiffAt
  · have hzero : ContDiffAt ℝ ∞ (fun _ : R3 => (0 : Half)) x := contDiffAt_const
    refine hzero.congr_of_eventuallyEq ?_
    filter_upwards [ActualHigherSFormation.notMem_tsupport_eventually hO hD F0 x hx] with z hz
    rw [hW0 z hz, map_zero]

/-- GLOBAL C^∞ of the lift, from the ambient germs and the membership-only premise. -/
theorem contDiff_reverseEHigherLift (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (R : RevRoom hreg δ0 W δ) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (j : Fin 3) :
    ContDiff ℝ ∞ (Vrev hreg δ0 W δr Ar p q F0 j) := by
  have hTs := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q
  have hU := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hUB := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F0)
  have hU0 := revInput_eq_zero hO hD F0
  have hUB0 := revDegreeInput_eq_zero hO hD F0
  have h1 := reverseE_family_apply L hO hD δr Ar p q hTs (DGE hreg δ0 W (Sum.inr ()) j) F0
    (fun x hx => R.germGen (Sum.inr ()) j _ (hT x hx)) (Uin F0) hU hU0
  have h2 := reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
    (fun x hx => R.germHigh j _ (hT x hx)) (UBin F0) hUB hUB0
  have h3 := reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
    (fun x hx => R.germHigh j _ (hT x hx)) (Uin F0) hU hU0
  exact (sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)).contDiff.comp ((h1.add h2).add h3)

theorem tsupport_reverseEHigherLift_subset (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (j : Fin 3) : tsupport (Vrev hreg δ0 W δr Ar p q F0 j) ⊆ TS F0 := by
  have hsupp : Function.support (Vrev hreg δ0 W δr Ar p q F0 j) ⊆ TS F0 := by
    intro z hz
    by_contra hz'
    exact (Function.mem_support.1 hz) (reverseEHigherLift_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δr Ar p q F0 j z hz')
  exact closure_minimal hsupp (isClosed_tsupport _)

theorem hasCompactSupport_reverseEHigherLift (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (j : Fin 3) : HasCompactSupport (Vrev hreg δ0 W δr Ar p q F0 j) :=
  IsCompact.of_isClosed_subset F0.property.2.1 (isClosed_tsupport _)
    (tsupport_reverseEHigherLift_subset g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δr Ar p q F0 j)

/-! ## 4. Exports: retained W, then ordinary W chosen exactly once -/

/-- The full lift contract on one fixed `δ`, for EVERY positive profile and finite input. -/
def ReverseEHigherLiftContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) : Prop :=
  ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → 0 < Ar → ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 →
  ∀ F0 : smoothCompactFiniteSphereCore hO hD,
    (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) → ∀ j : Fin 3,
      (∀ x : R3, IH (Vrev hreg δ0 W δr Ar p q F0 j x) = eH j ((Tq δr Ar p q) x) (Uin F0 x)) ∧
      ContDiff ℝ ∞ (Vrev hreg δ0 W δr Ar p q F0 j) ∧
      (∀ z ∉ TS F0, Vrev hreg δ0 W δr Ar p q F0 j z = 0) ∧
      HasCompactSupport (Vrev hreg δ0 W δr Ar p q F0 j)

/-- Retained-W producer: `δ` (with all discharged facts) is chosen BEFORE every profile. -/
theorem exists_retained_reverseE_higher_lift (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, RevRoom hreg δ0 W δ ∧
      ReverseEHigherLiftContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ := by
  obtain ⟨δ,R⟩ := exists_retained_reverseE_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg hKernel δ0 hδ0 W
  refine ⟨δ,R,?_⟩
  intro δr Ar p hδr hAr q _hq F0 hT j
  exact ⟨reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ R δr Ar p q F0 hT j,
    contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ R δr Ar p hδr hAr q F0 hT j,
    reverseEHigherLift_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δr Ar p q F0 j,
    hasCompactSupport_reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δr Ar p q F0 j⟩

/-- Ordinary actual packet: `δ0, W` selected exactly ONCE, then the retained producer. -/
theorem exists_actual_reverseE_higher_lift (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ ρ ∧ ∃ W : CoeffRoom δ0, ∃ δ : ℝ, RevRoom hreg δ0 W δ ∧
      ReverseEHigherLiftContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ := by
  obtain ⟨δ0,hδ0,hδ0ρ,_hRoom,W,_⟩ :=
    exists_commonRoom_actual_fullE_ordinary_endpoints g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨δ,R,hLift⟩ := exists_retained_reverseE_higher_lift g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg hKernel δ0 hδ0 W
  exact ⟨δ0,hδ0,hδ0ρ,W,δ,R,hLift⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseEHigherLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseEHigherLift.exists_actual_reverseE_higher_lift
