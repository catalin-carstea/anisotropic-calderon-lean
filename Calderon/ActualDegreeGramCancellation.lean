import Calderon.ActualCommonFirstWordQuadraticAdjoint
import Calderon.ActualHigherSPhysicalPairing
/- Root mathematical expansion is in UPFRONT.md, before this source. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualDegreeGramCancellation
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
@[instance_reducible] private def gramHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def gramHighModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def gramLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def gramLowModule : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] gramHighNormed gramHighModule gramLowNormed gramLowModule

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

local notation "GenRoom" => GeneratorEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CH" => pairedLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BG" => (Sum.inr () : Generator)

/-- Original physical degree is symmetric in the universal Half/Neg pivot. -/
theorem degree_low_pivot (u v : Half) :
    PP u (generatorLow BG v)=PP v (generatorLow BG u) := by
  have h := sphereSobolevDualPairing_lower_distributionalTranspose
    (sphereSobolevShiftedDegreeL (1/2 : ℝ)) v u
  rw [sphereLowerDistributionalTranspose_shiftedDegree_half] at h
  exact h

/-- Genuine forward-low/ordered-reverse-low pairing on ANY caller's W. -/
theorem low_reverse_pairing (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0)
    (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u v : Half) :
    PP u (EL i t v)=PP v (eL i t u) := by
  have hp := (W.piGerm i t ⟨hSub ht.1,ht.2⟩).self_of_nhds
  simpa only [reverseELow] using
    canonicalLow_explicit_ordered_reverse_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      i t (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
        hRoom t.1 ht.1) _ hp.2.1 hp.2.2 u v

/-- Literal full physical E/E Gram form; output is never projected or truncated. -/
def degreeGram (i j : Fin 3) (t : Tpar) (u v : Hi) : ℝ :=
  ⟪KL (EH i t u),KL (EH j t v)⟫_ℝ

attribute [local irreducible] canonicalHigh canonicalLow reverseEHigh reverseELow
  pairedLeftHigh generatorHigh generatorLow sphereSobolevInclusionL
  sphereSobolevHalfToSphereL2L degreeGram

private lemma sub_graph_rearrange {M : Type*} [AddCommGroup M] (a b c : M)
    (h : c=b-a) : a=b-c := by rw [h]; abel

/-- Genuine commutator graph on actual degree lifts, without any E-output degree lift. -/
theorem degree_lift_E_graph (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (P : GenRoom hreg δ0 W δ)
    (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0)
    (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u ub : Hi)
    (hb : IH ub=generatorHigh BG u) :
    JL (EH i t ub)=generatorLow BG (EH i t u)-JL (CH hreg δ0 W BG i t u) := by
  have hc := ActualCommonFirstWordQuadraticAdjoint.canonical_compat_anyW
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ hSub hRoom i t ht ub
  have hg1 : JL (CH hreg δ0 W BG i t u)=generatorLow BG (EH i t u)-EL i t (generatorHigh BG u) := by
    simpa only [generatorSharpLow,generatorSharpHigh] using P.highGraph BG i t ht u
  exact hc.trans ((congrArg (EL i t) hb).trans
    (sub_graph_rearrange _ _ _ hg1))

/-- Signed degree Gram cancellation: leading degree terms cancel before estimating. -/
theorem degree_gram_cancellation (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (P : GenRoom hreg δ0 W δ)
    (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0)
    (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u v ub vb : Hi)
    (hu : IH ub=generatorHigh BG u) (hv : IH vb=generatorHigh BG v) :
    degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t u vb-
      degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t ub v =
    PP (IH v) (eL j t (CH hreg δ0 W BG i t u))-
      PP (EH i t u) (P.low BG j t (IH v)) := by
  have hgi := degree_lift_E_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ P hSub hRoom i t ht u ub hu
  have hgj := degree_lift_E_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ P hSub hRoom j t ht v vb hv
  have hci := ActualCommonFirstWordQuadraticAdjoint.canonical_compat_anyW
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ hSub hRoom j t ht v
  have hupper := congrArg (fun A : Hi →L[ℝ] Neg => A v) (P.upper BG j t ht)
  change P.low BG j t (IH v)=JL (CH hreg δ0 W BG j t v) at hupper
  have hpair := low_reverse_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    δ0 W δ hSub hRoom j t ht (CH hreg δ0 W BG i t u) (IH v)
  have hsym := v016_pairing_inclusion_symm (EH j t v) (CH hreg δ0 W BG i t u)
  have hpiv := degree_low_pivot (EH i t u) (EH j t v)
  have hphys1 := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
    (EH i t u) (EH j t vb)
  have hphys2 := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
    (EH j t v) (EH i t ub)
  have hm : PP (EH j t v) (JL (CH hreg δ0 W BG i t u)) =
      PP (IH v) (eL j t (CH hreg δ0 W BG i t u)) :=
    hsym.trans ((congrArg (PP (CH hreg δ0 W BG i t u)) hci).trans hpair)
  have hsub (x : Half) (a b : Neg) : PP x (a-b)=PP x a-PP x b :=
    inner_sub_right x a b
  have hn1 := (congrArg (PP (EH i t u)) hgj).trans (hsub _ _ _)
  have hn2 := (congrArg (PP (EH j t v)) hgi).trans (hsub _ _ _)
  have hn3 := congrArg (PP (EH i t u)) hupper
  have hp2 : PP (EH j t v) (JL (EH i t ub))=
      ⟪KL (EH i t ub),KL (EH j t v)⟫_ℝ :=
    hphys2.trans (real_inner_comm _ _)
  unfold degreeGram
  calc
    _ = PP (EH i t u) (JL (EH j t vb))-PP (EH j t v) (JL (EH i t ub)) :=
      congrArg₂ (fun a b : ℝ => a-b) hphys1.symm hp2.symm
    _ = _ := by linarith only [hn1,hn2,hn3,hpiv,hm]

private lemma mixed_pairing_difference_bound
    (A : Half →L[ℝ] Neg) (C E : Hi →L[ℝ] Half) (D : Half →L[ℝ] Neg) (u : Hi) (v : Half) :
    |PP v (A (C u))-PP (E u) (D v)| ≤
      (‖A‖*‖C‖+‖E‖*‖D‖)*‖u‖*‖v‖ := by
  have h1 : |PP v (A (C u))| ≤ ‖v‖*(‖A‖*(‖C‖*‖u‖)) := by
    calc
      _ ≤ ‖v‖*‖A (C u)‖ := abs_sphereSobolevDualPairing_le (1/2 : ℝ) v (A (C u))
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((A.le_opNorm (C u)).trans (mul_le_mul_of_nonneg_left (C.le_opNorm u) (norm_nonneg A)))
        (norm_nonneg v)
  have h2 : |PP (E u) (D v)| ≤ (‖E‖*‖u‖)*(‖D‖*‖v‖) :=
    (abs_sphereSobolevDualPairing_le (1/2 : ℝ) (E u) (D v)).trans
      (mul_le_mul (E.le_opNorm u) (D.le_opNorm v) (norm_nonneg _) (mul_nonneg (norm_nonneg E) (norm_nonneg u)))
  calc
    _ ≤ |PP v (A (C u))|+|PP (E u) (D v)| := abs_sub _ _
    _ ≤ ‖v‖*(‖A‖*(‖C‖*‖u‖))+(‖E‖*‖u‖)*(‖D‖*‖v‖) := add_le_add h1 h2
    _ = _ := by ring

/-- Mixed Hi/Half bound after genuine signed degree cancellation. -/
theorem degree_gram_cancellation_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (P : GenRoom hreg δ0 W δ)
    (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0)
    (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u v ub vb : Hi)
    (hu : IH ub=generatorHigh BG u) (hv : IH vb=generatorHigh BG v) :
    |degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t u vb-
      degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t ub v| ≤
      (‖eL j t‖*‖CH hreg δ0 W BG i t‖+‖EH i t‖*‖P.low BG j t‖)*‖u‖*‖IH v‖ :=
  (congrArg abs (degree_gram_cancellation g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ P hSub hRoom i j t ht u v ub vb hu hv)).le.trans
    (mixed_pairing_difference_bound (eL j t) (CH hreg δ0 W BG i t) (EH i t) (P.low BG j t) u (IH v))

private lemma exists_finite_norm_cap {ι X E : Type*} [Fintype ι] [TopologicalSpace X]
    [NormedAddCommGroup E] (K : Set X) (hK : IsCompact K) (f : ι → X → E)
    (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i x, x ∈ K → ‖f i x‖ ≤ M := by
  classical
  have hb (i : ι) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ‖f i x‖ ≤ M := by
    obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (hf i)
    exact ⟨max 0 M,le_max_left _ _,fun x hx => (hM x hx).trans (le_max_right _ _)⟩
  choose M hM0 hM using hb
  refine ⟨∑ i, M i,Finset.sum_nonneg (fun i _ => hM0 i),?_⟩
  intro i x hx
  exact (hM i x hx).trans (Finset.single_le_sum (fun j _ => hM0 j) (Finset.mem_univ i))

/-- The native paired packet already provides degree high/low value caps. -/
theorem exists_degree_commutator_value_caps (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP) :
    ∃ CG : ℝ, 0 ≤ CG ∧ ∀ i : Fin 3, ∀ t ∈ ParamRoom δP,
      ‖CH hreg δ0 W BG i t‖ ≤ CG ∧ ‖P.low BG i t‖ ≤ CG := by
  obtain ⟨CG,hCG,hG⟩ := P.finiteCaps 0
  refine ⟨CG,hCG,?_⟩
  intro i t ht
  have h := hG BG i 0 (le_refl 0) t ht
  exact ⟨by simpa only [norm_iteratedFDerivWithin_zero] using h.1,
    by simpa only [norm_iteratedFDerivWithin_zero] using h.2.2⟩

/-- Compact actual operator budget, isolated from room production and graph conversion. -/
theorem exists_degree_gram_operator_budget (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δ : ℝ) (hPP : ParamRoom δ ⊆ ParamRoom δP)
    (he : ∀ i : Fin 3, ContinuousOn (eL i) (ParamRoom δ))
    (hE : ∀ i : Fin 3, ContinuousOn (EH i) (ParamRoom δ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
      ‖eL j t‖*‖CH hreg δ0 W BG i t‖+‖EH i t‖*‖P.low BG j t‖ ≤ K := by
  have hK := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  obtain ⟨Ce,hCe,heCap⟩ := exists_finite_norm_cap (ι := Fin 3) (X := Tpar) (E := Half →L[ℝ] Neg)
    (ParamRoom δ) hK (fun i => eL i) he
  obtain ⟨CE,hCE,hECap⟩ := exists_finite_norm_cap (ι := Fin 3) (X := Tpar) (E := Hi →L[ℝ] Half)
    (ParamRoom δ) hK (fun i => EH i) hE
  obtain ⟨CG,hCG,hGCap⟩ := exists_degree_commutator_value_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P
  refine ⟨Ce*CG+CE*CG,add_nonneg (mul_nonneg hCe hCG) (mul_nonneg hCE hCG),?_⟩
  intro i j t ht
  exact add_le_add (mul_le_mul (heCap j t ht) (hGCap i t (hPP ht)).1 (norm_nonneg _) hCe)
    (mul_le_mul (hECap i t ht) (hGCap j t (hPP ht)).2 (norm_nonneg _) hCE)

/-- Uniform actual cancellation on ANY retained W; constants precede all profiles and inputs.
The paired room is discharged internally, not supplied as an analytic premise. -/
theorem exists_retained_degree_gram_cancellation_bound (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u v ub vb : Hi,
      IH ub=generatorHigh BG u → IH vb=generatorHigh BG v →
      |degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t u vb-
        degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t ub v| ≤ K*‖u‖*‖IH v‖ := by
  have hPairedFull := exists_retained_generator_paired_endpoints
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hPairedFull with ⟨dP,hdP,hdP0,hdPρ,hRoomP,⟨P⟩⟩
  have hReverseFull := ActualReverseEHigherLift.exists_retained_reverseE_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hReverseFull with ⟨dR,R⟩
  let δ := min dP dR
  have hδ : 0 < δ := lt_min hdP R.pos
  have hδP : δ ≤ dP := min_le_left _ _
  have hδR : δ ≤ dR := min_le_right _ _
  have hSP := commonRoom_mono y0 ρ hδP
  have hSR := commonRoom_mono y0 ρ hδR
  have hP0 := commonRoom_mono y0 ρ hdP0
  have hPP : ParamRoom δ ⊆ ParamRoom dP := fun t ht => ⟨hSP ht.1,ht.2⟩
  have hPR : ParamRoom δ ⊆ ParamRoom dR := fun t ht => ⟨hSR ht.1,ht.2⟩
  have he (i : Fin 3) : ContinuousOn (eL i) (ParamRoom δ) := fun t ht =>
    (R.germLow i t (hPR ht)).continuousAt.continuousWithinAt
  have hE (i : Fin 3) : ContinuousOn (EH i) (ParamRoom δ) := fun t ht =>
    ((ActualCommonFirstWordQuadraticAdjoint.canonical_ambient_contDiffAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W dP hP0 hRoomP
      i t (hPP ht)).1).continuousAt.continuousWithinAt
  obtain ⟨K,hK,hBudget⟩ := exists_degree_gram_operator_budget
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W dP P δ hPP he hE
  refine ⟨δ,hδ,hδP.trans hdP0,hδP.trans hdPρ,K,hK,?_⟩
  intro i j t ht u v ub vb hu hv
  have hBound := degree_gram_cancellation_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W dP P hP0 hRoomP i j t (hPP ht) u v ub vb hu hv
  exact hBound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hBudget i j t ht) (norm_nonneg u)) (norm_nonneg (IH v)))

local notation "UBin" => ActualHigherSFormation.higherSDegreeInput hO hD

/-- The original finite core discharges the genuine physical degree-lift premise. -/
theorem finite_degree_input_inclusion (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    IH (UBin F0 x)=generatorHigh BG (Uin F0 x) := by
  simpa only [generatorHigh,ActualHigherSFormation.higherSDegreeInput,ActualHigherSFormation.higherSInput]
    using inclusion_finiteCoreSobolevLift_coreDegree hO hD F0 x

/-- Fully actual finite-input cancellation estimate; no new regularity or lift assumptions. -/
theorem exists_retained_finite_degree_gram_bound (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
      ∀ F0 G0 : smoothCompactFiniteSphereCore hO hD, ∀ x y : R3,
      |degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t (Uin F0 x) (UBin G0 y)-
        degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t (UBin F0 x) (Uin G0 y)| ≤
        K*‖Uin F0 x‖*‖IH (Uin G0 y)‖ := by
  have hFull := exists_retained_degree_gram_cancellation_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hFull with ⟨δ,hδ,hδ0le,hδρ,K,hK,hBound⟩
  refine ⟨δ,hδ,hδ0le,hδρ,K,hK,?_⟩
  intro i j t ht F0 G0 x y
  exact hBound i j t ht (Uin F0 x) (Uin G0 y) (UBin F0 x) (UBin G0 y)
    (finite_degree_input_inclusion hO hD F0 x) (finite_degree_input_inclusion hO hD G0 y)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualDegreeGramCancellation
