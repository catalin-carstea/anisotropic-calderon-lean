import Calderon.ActualHighSharpMultiplierTaylorGraph
import Calderon.ActualRaisingEHighGraph

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedCanonicalMultiplierGains
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualRetainedGeneratorMultiplierGains ActualRaisingEHighGainedEndpoints
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def mixedHiNormed : NormedAddCommGroup (Hi →L[ℝ] Hi) := inferInstance
@[instance_reducible] private def mixedHiModule : NormedSpace ℝ (Hi →L[ℝ] Hi) := inferInstance
@[instance_reducible] private def mixedHalfNormed : NormedAddCommGroup (Half →L[ℝ] Half) := inferInstance
@[instance_reducible] private def mixedHalfModule : NormedSpace ℝ (Half →L[ℝ] Half) := inferInstance
attribute [local instance] mixedHiNormed mixedHiModule mixedHalfNormed mixedHalfModule

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private lemma lowering_multiplier_graph
    (I : E →L[ℝ] F) (MH : Fin 3 → E →L[ℝ] E) (ML : Fin 3 → F →L[ℝ] F)
    (R : Fin 3 → E →L[ℝ] F) (B : E →L[ℝ] F)
    (PH : E →L[ℝ] E) (PL : F →L[ℝ] F)
    (GR : Fin 3 → E →L[ℝ] E) (GB : E →L[ℝ] E) (i : Fin 3)
    (hM : ∀ j x, I ((MH j) x)=(ML j) (I x))
    (hR : ∀ j x, I (GR j x)=R j (PH x)-PL (R j x))
    (hB : ∀ x, I (GB x)=B (PH x)-PL (B x))
    (hC : ∀ j x, (ML j) (PL x)=PL ((ML j) x)) (x : E) :
    I (((∑ j : Fin 3, (MH j).comp (GR j))+(MH i).comp GB) x) =
      ((∑ j : Fin 3, (ML j).comp (R j))+(ML i).comp B) (PH x)-
        PL (((∑ j : Fin 3, (ML j).comp (R j))+(ML i).comp B) x) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,map_add,map_sum,hM,hR,hB,map_sub,hC,
    Finset.sum_sub_distrib]
  abel
end Generic

private lemma finite_family_norm_cap {I X V : Type*} [Fintype I]
    [TopologicalSpace X] [NormedAddCommGroup V]
    (K : Set X) (hK : IsCompact K) (f : I → X → V)
    (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ x ∈ K, ‖f i x‖ ≤ C := by
  classical
  have hEx (i : I) := hK.exists_bound_of_continuousOn (f := f i) (hf i)
  choose b hb using hEx
  refine ⟨∑ i, |b i|,Finset.sum_nonneg (fun i _ => abs_nonneg _),?_⟩
  intro i x hx
  exact (hb i x hx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun i _ => abs_nonneg (b i)) (Finset.mem_univ i)))

private lemma use_finite_family_caps {I X V Z : Type*} [Fintype I]
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedAddCommGroup Z]
    (K : Set X) (hK : IsCompact K) (f : I → X → V) (g : I → X → Z)
    (hf : ∀ i, ContinuousOn (f i) K) (hg : ∀ i, ContinuousOn (g i) K)
    {Result : Prop}
    (use : ∀ C : ℝ, 0 ≤ C → (∀ i, ∀ x ∈ K, ‖f i x‖ ≤ C ∧ ‖g i x‖ ≤ C) → Result) :
    Result := by
  obtain ⟨Cf,hCf,hfB⟩ := finite_family_norm_cap K hK f hf
  obtain ⟨Cg,hCg,hgB⟩ := finite_family_norm_cap K hK g hg
  exact use (Cf+Cg) (add_nonneg hCf hCg) (fun i x hx =>
    ⟨(hfB i x hx).trans (le_add_of_nonneg_right hCg),
      (hgB i x hx).trans (le_add_of_nonneg_left hCf)⟩)

private lemma use_generator_room (S G K : ℝ → Prop) (d0 r : ℝ) {Result : Prop}
    (h : ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ r ∧ S d ∧ G d ∧ K d)
    (f : ∀ d : ℝ, 0 < d → d ≤ d0 → d ≤ r → S d → G d → Result) : Result := by
  rcases h with ⟨d,hd,hd0,hdr,hS,hG,_hK⟩
  exact f d hd hd0 hdr hS hG

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
local notation "MH" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
local notation "ML" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
local notation "RH" j:max i:max => sphereSobolevRotationL (3/2 : ℝ) j i
local notation "RL" j:max i:max => sphereSobolevRotationL (1/2 : ℝ) j i
local notation "BH" => (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
local notation "BL" => (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0

/-- Genuine half coordinate/native multiplier commutation, transported on singles and extended by density. -/
lemma coordinate_native_half_comm (Q : SmoothCoefficientJets 3) (j : Fin 3) (v : Half) :
    (ML j) (NL (smoothMultiplierLowerJets Q) v)=
      NL (smoothMultiplierLowerJets Q) ((ML j) v) := by
  have hCLM : (ML j).comp (NL (smoothMultiplierLowerJets Q))=
      (NL (smoothMultiplierLowerJets Q)).comp (ML j) := by
    apply sphereSobolev_clm_eq_of_single (1/2 : ℝ)
    intro k u
    have he := congrArg IH (coordinate_native_high_comm hF hO hD hcalc τ0 Q j
      (sphereSobolevSingleL (3/2 : ℝ) k u))
    have hm (x : Hi) : IH ((MH j) x)=(ML j) (IH x) :=
      sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
        (by norm_num) (EuclideanSpace.single j 1) x
    have hn (x : Hi) : IH (NH Q x)=NL (smoothMultiplierLowerJets Q) (IH x) :=
      v017_native_high_half hcalc hF hO hD τ0 Q x
    simpa only [ContinuousLinearMap.comp_apply,hm,hn,sphereSobolevInclusionL_single] using he
  exact congrArg (fun T : Half →L[ℝ] Half => T v) hCLM

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GH" => retainedGeneratorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GL" => retainedGeneratorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Original lowering/retained multiplier zero-order gain on the high endpoint. -/
def loweringMultiplierHigh (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3)
    (c : RetainedCoefficient) (t : Tpar) : Hi →L[ℝ] Hi :=
  (∑ j : Fin 3, (MH j).comp (GH δ0 W (Sum.inl (j,i)) c t))+
    (MH i).comp (GH δ0 W (Sum.inr ()) c t)

/-- Original raising/retained multiplier zero-order gain on the genuine half endpoint. -/
def raisingMultiplierHalf (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3)
    (c : RetainedCoefficient) (t : Tpar) : Half →L[ℝ] Half :=
  (-∑ j : Fin 3, (GL δ0 W (Sum.inl (j,i)) c t).comp (ML j))+
    (GL δ0 W (Sum.inr ()) c t).comp (ML i)
local notation "LH" => loweringMultiplierHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "RA" => raisingMultiplierHalf hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

attribute [local irreducible] loweringHigh loweringLow raisingHigh raisingLow
  loweringMultiplierHigh raisingMultiplierHalf
  retainedGeneratorHigh retainedGeneratorHalf retainedJets sphereSobolevInclusionL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL

/-- Actual lowering high graph, with only native generator graphs as internal inputs. -/
lemma loweringMultiplierHigh_graph (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3)
    (c : RetainedCoefficient) (t : Tpar)
    (hRot : ∀ j x, IH (GH δ0 W (Sum.inl (j,i)) c t x)=
      (RH j i) (NH (QW δ0 W c t) x)-NL (smoothMultiplierLowerJets (QW δ0 W c t)) ((RH j i) x))
    (hDeg : ∀ x, IH (GH δ0 W (Sum.inr ()) c t x)=
      BH (NH (QW δ0 W c t) x)-NL (smoothMultiplierLowerJets (QW δ0 W c t)) (BH x))
    (x : Hi) :
    IH (LH δ0 W i c t x)=loweringHigh hF hO hD i (NH (QW δ0 W c t) x)-
      NL (smoothMultiplierLowerJets (QW δ0 W c t)) (loweringHigh hF hO hD i x) := by
  have he := lowering_multiplier_graph IH (fun j => MH j) (fun j => ML j)
    (fun j => RH j i) BH (NH (QW δ0 W c t)) (NL (smoothMultiplierLowerJets (QW δ0 W c t)))
    (fun j => GH δ0 W (Sum.inl (j,i)) c t) (GH δ0 W (Sum.inr ()) c t) i
    (fun j v => sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (EuclideanSpace.single j 1) v)
    hRot hDeg (fun j v => coordinate_native_half_comm hF hO hD hcalc τ0 (QW δ0 W c t) j v) x
  simpa only [loweringMultiplierHigh,loweringHigh] using he

/-- Actual half raising graph, with no inferred inverse inclusion. -/
lemma raisingMultiplierHalf_graph (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3)
    (c : RetainedCoefficient) (t : Tpar)
    (hRot : ∀ j x, JL (GL δ0 W (Sum.inl (j,i)) c t x)=
      (RL j i) (NL (smoothMultiplierLowerJets (QW δ0 W c t)) x)-
        NN (smoothMultiplierLowerJets (QW δ0 W c t)) ((RL j i) x))
    (hDeg : ∀ x, JL (GL δ0 W (Sum.inr ()) c t x)=
      BL (NL (smoothMultiplierLowerJets (QW δ0 W c t)) x)-
        NN (smoothMultiplierLowerJets (QW δ0 W c t)) (BL x))
    (x : Half) :
    JL (RA δ0 W i c t x)=raisingLow hF hO hD i (NL (smoothMultiplierLowerJets (QW δ0 W c t)) x)-
      NN (smoothMultiplierLowerJets (QW δ0 W c t)) (raisingLow hF hO hD i x) := by
  have he := raisingMultiplier_cancel JL (fun j => RL j i) BL (fun j => ML j)
    (NL (smoothMultiplierLowerJets (QW δ0 W c t))) (NN (smoothMultiplierLowerJets (QW δ0 W c t)))
    (fun j => GL δ0 W (Sum.inl (j,i)) c t) (GL δ0 W (Sum.inr ()) c t) i
    hRot hDeg (fun j v => coordinate_native_half_comm hF hO hD hcalc τ0 (QW δ0 W c t) j v) x
  simpa only [raisingMultiplierHalf,raisingLow] using he

/-- Same original room and one cap, before every retained coefficient and angular input.
All native generator callbacks in the internal graphs are discharged here. -/
private def mixedGainsContract (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ CM : ℝ, 0 ≤ CM ∧
      (∀ i : Fin 3, ∀ c : RetainedCoefficient,
        ContDiffOn ℝ ∞ (LH δ0 W i c) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (RA δ0 W i c) (ParamRoom δ)) ∧
      (∀ i : Fin 3, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
        (∀ x : Hi, IH (LH δ0 W i c t x)=loweringHigh hF hO hD i (NH (QW δ0 W c t) x)-
          NL (smoothMultiplierLowerJets (QW δ0 W c t)) (loweringHigh hF hO hD i x)) ∧
        (∀ x : Half, JL (RA δ0 W i c t x)=raisingLow hF hO hD i
          (NL (smoothMultiplierLowerJets (QW δ0 W c t)) x)-
          NN (smoothMultiplierLowerJets (QW δ0 W c t)) (raisingLow hF hO hD i x))) ∧
      (∀ i : Fin 3, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
        ‖LH δ0 W i c t‖ ≤ CM ∧ ‖RA δ0 W i c t‖ ≤ CM)

attribute [local irreducible] mixedGainsContract

private theorem mixedGainsContract_proof
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    mixedGainsContract hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg δ0 W := by
  unfold mixedGainsContract
  trace "mixed-room-entered"
  apply use_generator_room
    (fun δ : ℝ => ∀ V : Generator, ∀ c : RetainedCoefficient,
        ContDiffOn ℝ ∞ (GH δ0 W V c) (ParamRoom δ) ∧ ContDiffOn ℝ ∞ (GL δ0 W V c) (ParamRoom δ))
    (fun δ : ℝ => ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
        (∀ u : Hi, IH (GH δ0 W V c t u)=generatorHigh V (NH (QW δ0 W c t) u)-
          NL (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorHigh V u)) ∧
        (∀ v : Half, JL (GL δ0 W V c t v)=generatorLow V (NL (smoothMultiplierLowerJets (QW δ0 W c t)) v)-
          NN (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorLow V v)))
    (fun δ : ℝ => ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ n : ℕ, n ≤ N →
        ∀ t ∈ ParamRoom δ,
          ‖iteratedFDerivWithin ℝ n (GH δ0 W V c) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (GL δ0 W V c) (ParamRoom δ) t‖ ≤ M)
    δ0 ρ
    (exists_commonRoom_retained_generator_multiplier_gains
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W)
  intro δ hδ hδ0le hδρ hUS hUG
  trace "mixed-room-unpacked"
  have hLH (i : Fin 3) (c : RetainedCoefficient) :
      ContDiffOn ℝ ∞ (LH δ0 W i c) (ParamRoom δ) := by
    unfold loweringMultiplierHigh
    exact (ContDiffOn.sum (fun j _ => contDiffOn_const.clm_comp (hUS (Sum.inl (j,i)) c).1)).add
      (contDiffOn_const.clm_comp (hUS (Sum.inr ()) c).1)
  have hRA (i : Fin 3) (c : RetainedCoefficient) :
      ContDiffOn ℝ ∞ (RA δ0 W i c) (ParamRoom δ) := by
    unfold raisingMultiplierHalf
    exact ((ContDiffOn.sum (fun j _ => (hUS (Sum.inl (j,i)) c).2.clm_comp contDiffOn_const)).neg).add
      ((hUS (Sum.inr ()) c).2.clm_comp contDiffOn_const)
  trace "mixed-smooth-proved"
  have hK : IsCompact (ParamRoom δ) :=
    (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  trace "mixed-compact-proved"
  apply use_finite_family_caps (ParamRoom δ) hK
    (fun z : Fin 3 × RetainedCoefficient => LH δ0 W z.1 z.2)
    (fun z : Fin 3 × RetainedCoefficient => RA δ0 W z.1 z.2)
    (fun z => (hLH z.1 z.2).continuousOn) (fun z => (hRA z.1 z.2).continuousOn)
  intro CM hCM hCaps
  trace "mixed-caps-proved"
  refine ⟨δ,hδ,hδ0le,hδρ,CM,hCM,fun i c => ⟨hLH i c,hRA i c⟩,?_,?_⟩
  · intro i c t ht
    trace "mixed-graphs-entered"
    exact ⟨loweringMultiplierHigh_graph hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg δ0 W i c t
        (fun j => by simpa only [generatorHigh] using (hUG (Sum.inl (j,i)) c t ht).1)
        (by simpa only [generatorHigh] using (hUG (Sum.inr ()) c t ht).1),
      raisingMultiplierHalf_graph hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg δ0 W i c t
        (fun j => by simpa only [generatorLow] using (hUG (Sum.inl (j,i)) c t ht).2)
        (by simpa only [generatorLow] using (hUG (Sum.inr ()) c t ht).2)⟩
  · intro i c t ht
    exact hCaps (i,c) t ht


theorem exists_commonRoom_actual_mixed_multiplier_gains
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ CM : ℝ, 0 ≤ CM ∧
      (∀ i : Fin 3, ∀ c : RetainedCoefficient,
        ContDiffOn ℝ ∞ (LH δ0 W i c) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (RA δ0 W i c) (ParamRoom δ)) ∧
      (∀ i : Fin 3, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
        (∀ x : Hi, IH (LH δ0 W i c t x)=loweringHigh hF hO hD i (NH (QW δ0 W c t) x)-
          NL (smoothMultiplierLowerJets (QW δ0 W c t)) (loweringHigh hF hO hD i x)) ∧
        (∀ x : Half, JL (RA δ0 W i c t x)=raisingLow hF hO hD i
          (NL (smoothMultiplierLowerJets (QW δ0 W c t)) x)-
          NN (smoothMultiplierLowerJets (QW δ0 W c t)) (raisingLow hF hO hD i x))) ∧
      (∀ i : Fin 3, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
        ‖LH δ0 W i c t‖ ≤ CM ∧ ‖RA δ0 W i c t‖ ≤ CM) := by
  simpa only [mixedGainsContract] using
    (mixedGainsContract_proof hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg hKernel δ0 hδ0 W)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedCanonicalMultiplierGains
