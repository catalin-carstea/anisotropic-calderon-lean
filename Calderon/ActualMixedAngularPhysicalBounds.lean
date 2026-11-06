import Calderon.ActualMixedAngularPairedBounds
import Calderon.ActualFullEPhysicalEndpoints
import Calderon.ActualHigherSLeadingWeightedJetBounds

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualMixedCanonicalMultiplierGains
  ActualRetainedGeneratorMultiplierGains ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualCanonicalAngularGainedBracket NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "TH" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "TL" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "SH" => referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "SL" => referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "LH" => loweringMultiplierHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "RA" => raisingMultiplierHalf hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CT" => loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CS" => raisingAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "KK" => gainedAtOrder hF hO hD (3/2 : ℝ)
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

local notation "CH" => loweringEHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "HH" => raisingReverseHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "ΩH" => referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc
open ActualGeneratorRadialGainedRows
attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL loweringMultiplierHigh raisingMultiplierHalf
  loweringEHigh raisingReverseHigh


open FixedParameterProfilePullback FixedParameterProfileBudgets ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q


/-- Actual physical caps and exact diagrams, at the original profile point. -/
def mixedPhysicalEndpointData (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (G : Fin 3 → Pphys → Half →L[ℝ] Half) (Bl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg)
    (M KT dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) : Prop :=
  ∀ i j : Fin 3,
    physicalEndpointFirstCaps (L := L) (CH hreg G δ0 W i j) dr Ar p q x M KT ∧
    physicalEndpointFirstCaps (L := L) (HH hreg δ0 W i j) dr Ar p q x M KT ∧
    physicalEndpointFirstCaps (L := L) (Bl i j) dr Ar p q x M KT ∧
    (∀ u : Hi, JL (CH hreg G δ0 W i j ((Tq dr Ar p q) x) u)=
      aL i (EH j ((Tq dr Ar p q) x) u)-EL j ((Tq dr Ar p q) x) (aH i u)) ∧
    (∀ u : Hi, JL (HH hreg δ0 W i j ((Tq dr Ar p q) x) u)=
      AL i (eH j ((Tq dr Ar p q) x) u)-eL j ((Tq dr Ar p q) x) (AH i u)) ∧
    (Bl i j ((Tq dr Ar p q) x)).comp IH=(JL).comp (CH hreg G δ0 W i j ((Tq dr Ar p q) x)) ∧
    (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Bl i j ((Tq dr Ar p q) x))=
      (v016TransposeL (-(HH hreg δ0 W i j ((Tq dr Ar p q) x)))).comp JL

/-- Original caller-W mixed endpoints, with physical uniformity before every profile choice. -/
structure MixedAngularPhysicalEndpointRoom (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le0 : δ ≤ δ0
  δ_le : δ ≤ ρ
  G : Fin 3 → Pphys → Half →L[ℝ] Half
  Bl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg
  smooth : ∀ i j : Fin 3,
    ContDiffOn ℝ ∞ (CH hreg G δ0 W i j) (ParamRoom δ) ∧
    ContDiffOn ℝ ∞ (HH hreg δ0 W i j) (ParamRoom δ) ∧
    ContDiffOn ℝ ∞ (Bl i j) (ParamRoom δ)
  graphs : ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
    (∀ u : Hi, JL (CH hreg G δ0 W i j t u)=aL i (EH j t u)-EL j t (aH i u)) ∧
    (∀ u : Hi, JL (HH hreg δ0 W i j t u)=AL i (eH j t u)-eL j t (AH i u)) ∧
    (Bl i j t).comp IH=(JL).comp (CH hreg G δ0 W i j t) ∧
    (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Bl i j t)=
      (v016TransposeL (-(HH hreg δ0 W i j t))).comp JL
  joint_caps : ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ,
    ‖iteratedFDerivWithin ℝ n (CH hreg G δ0 W i j) (ParamRoom δ) t‖ ≤ M ∧
    ‖iteratedFDerivWithin ℝ n (HH hreg δ0 W i j) (ParamRoom δ) t‖ ≤ M ∧
    ‖iteratedFDerivWithin ℝ n (Bl i j) (ParamRoom δ) t‖ ≤ M
  M : ℝ
  M_nonneg : 0 ≤ M
  KT : ℝ
  KT_pos : 0 < KT
  eta0 : ℝ
  eta0_pos : 0 < eta0
  eta0_le : eta0 ≤ 1
  physical_caps : ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
    ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
    1 ≤ actualReferenceBeta g L q dr Ar p x →
    referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
    mixedPhysicalEndpointData hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W G Bl M KT dr Ar p q x

/-- Rebuilt from the public pullback theorem: Main's same conversion helper is private. -/
private lemma mixed_physical_first_caps {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Tpar → V) (δ M KT : ℝ) (hM : 0 ≤ M)
    (hf : ContDiffOn ℝ ∞ f (ParamRoom δ)) (hU : UniqueDiffOn ℝ (ParamRoom δ))
    (hcap : ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom δ,
      ‖iteratedFDerivWithin ℝ n f (ParamRoom δ) t‖ ≤ M)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (hT : ContDiffAt ℝ ∞ (Tq dr Ar p q) x)
    (hmem : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (hTcap : ‖fderiv ℝ (Tq dr Ar p q) x‖ ≤ KT) :
    physicalEndpointFirstCaps (L := L) f dr Ar p q x M KT := by
  have hx := hmem.self_of_nhds
  have hc := physical_pullback_first_caps f (Tq dr Ar p q) (ParamRoom δ) x
    (hf _ hx) hT hmem (hU _ hx) M (hcap 0 (by omega) _ hx) (hcap 1 (by omega) _ hx)
  exact ⟨hc.1,hc.2.1,hc.2.2.trans (mul_le_mul_of_nonneg_left hTcap hM)⟩

private lemma use_smooth_endpoint_room {D G V : Type*}
    {A B C : D → Prop} {S Q N : D → G → V → Prop} {Result : Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ g : G, ∃ v : V,
      S d g v ∧ Q d g v ∧ N d g v)
    (use : ∀ d g v, A d → B d → C d → S d g v → Q d g v → N d g v → Result) : Result := by
  rcases h with ⟨d,ha,hb,hc,g,v,hs,hq,hn⟩
  exact use d g v ha hb hc hs hq hn

/-- No regularity, graph, bound or profile membership callback remains. -/
theorem exists_actual_mixedAngular_physical_endpoint_room (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    Nonempty (MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W) := by
  classical
  apply use_smooth_endpoint_room
    (exists_commonRoom_actual_mixedAngular_smooth_caps
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg hKernel δ0 hδ0 W)
  intro δ G Bl hδ hδ0le hδρ hSm hGraph hCaps
  let capWitness := hCaps 1
  let M : ℝ := Classical.choose capWitness
  have capFacts := Classical.choose_spec capWitness
  have hM := capFacts.1
  have hcap := capFacts.2
  let K := closedBall y0 ρ
  have hK : IsCompact K := isCompact_closedBall _ _
  let derivativeWitness := exists_uniform_higherSParam_derivative_bound g hg L hL K hK
  let KT : ℝ := Classical.choose derivativeWitness
  have derivativeFacts := Classical.choose_spec derivativeWitness
  have hKT := derivativeFacts.1
  have hTbound := derivativeFacts.2
  let guardWitness := exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ δ hδ K hK
  let eta0 : ℝ := Classical.choose guardWitness
  have guardFacts := Classical.choose_spec guardWitness
  have heta0 := guardFacts.1
  have heta01 := guardFacts.2.1
  have hguard := guardFacts.2.2
  have hU : UniqueDiffOn ℝ (ParamRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _) ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  refine ⟨{
    δ := δ
    δ_pos := hδ
    δ_le0 := hδ0le
    δ_le := hδρ
    G := G
    Bl := Bl
    smooth := hSm
    graphs := hGraph
    joint_caps := hCaps
    M := M
    M_nonneg := hM
    KT := KT
    KT_pos := hKT
    eta0 := eta0
    eta0_pos := heta0
    eta0_le := heta01
    physical_caps := ?_
  }⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0le x hx hxBall hb hs i j
  have hGuard := hguard q hq dr hdr hdr1 Ar hAr p hp eta heta heta0le x hx hxBall hb hs
  have hmem := higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x hGuard
  have hxT := hmem.self_of_nhds
  have hT : ContDiffAt ℝ ∞ (Tq dr Ar p q) x :=
    (contDiff_radiusProfileMap q (referenceRadius dr Ar p L)
      (contDiff_referenceRadius_actual dr Ar p L hdr hAr)).contDiffAt
  have hTc := hTbound q hq dr hdr hdr1 Ar hAr p hp eta heta (heta0le.trans heta01) x hx hb hs
  have hAt := hGraph i j _ hxT
  refine ⟨?_,?_,?_,hAt.1,hAt.2.1,hAt.2.2.1,hAt.2.2.2⟩
  · exact mixed_physical_first_caps (L := L) (y0 := y0) (ρ := ρ)
      _ δ M KT hM (hSm i j).1 hU (fun n hn t ht => (hcap i j n hn t ht).1)
      dr Ar p q x hT hmem hTc
  · exact mixed_physical_first_caps (L := L) (y0 := y0) (ρ := ρ)
      _ δ M KT hM (hSm i j).2.1 hU (fun n hn t ht => (hcap i j n hn t ht).2.1)
      dr Ar p q x hT hmem hTc
  · exact mixed_physical_first_caps (L := L) (y0 := y0) (ρ := ρ)
      _ δ M KT hM (hSm i j).2.2 hU (fun n hn t ht => (hcap i j n hn t ht).2.2)
      dr Ar p q x hT hmem hTc

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
