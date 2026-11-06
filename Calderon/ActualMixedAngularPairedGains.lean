import Calderon.ActualMixedCanonicalMultiplierGains
import Calderon.ActualFullEGainedPairedCore

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

section Algebra
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private lemma lowering_forward_assembly
    (I : E →L[ℝ] F) (J : F →L[ℝ] G)
    (aH : E →L[ℝ] F) (aL : F →L[ℝ] G)
    (TH : E →L[ℝ] F) (TL : F →L[ℝ] G)
    (PH : E →L[ℝ] E) (PL : F →L[ℝ] F)
    (NH : Fin 3 → E →L[ℝ] E) (NL : Fin 3 → F →L[ℝ] F)
    (AH : Fin 3 → E →L[ℝ] F) (AL : Fin 3 → F →L[ℝ] G)
    (ZH : E →L[ℝ] E) (ZL : F →L[ℝ] F)
    (CT : E →L[ℝ] F) (GP : E →L[ℝ] E)
    (KN : Fin 3 → E →L[ℝ] F) (GN : Fin 3 → E →L[ℝ] E)
    (ha : ∀ x, J (aH x)=aL (I x))
    (hT : ∀ x, J (TH x)=TL (I x))
    (hA : ∀ m x, J (AH m x)=AL m (I x))
    (hCT : ∀ x, J (CT x)=aL (TH x)-TL (aH x))
    (hGP : ∀ x, I (GP x)=aH (PH x)-PL (aH x))
    (hKN : ∀ m x, J (KN m x)=aL (AH m x)-AL m (aH x))
    (hGN : ∀ m x, I (GN m x)=aH (NH m x)-NL m (aH x)) (x : E) :
    J (CT (PH x)+TH (GP x)+
      (∑ m : Fin 3, (KN m (NH m x)+AH m (GN m x)))+
        aH (ZH x)-ZL (aH x)) =
      aL (TH (PH x)+(∑ m : Fin 3, AH m (NH m x))+I (ZH x))-
        (TL (PL (aH x))+(∑ m : Fin 3, AL m (NL m (aH x)))+J (ZL (aH x))) := by
  simp only [map_add,map_sub,map_sum,hCT,hT,hGP,hKN,hA,hGN,ha,Finset.sum_sub_distrib,Fin.sum_univ_three]
  abel

private lemma raising_reverse_assembly
    (I : E →L[ℝ] F) (J : F →L[ℝ] G)
    (AH : E →L[ℝ] F) (AL : F →L[ℝ] G)
    (SH : E →L[ℝ] F) (SL : F →L[ℝ] G)
    (PL : F →L[ℝ] F) (PN : G →L[ℝ] G)
    (NL : Fin 3 → F →L[ℝ] F) (NN : Fin 3 → G →L[ℝ] G)
    (aH : Fin 3 → E →L[ℝ] F) (aL : Fin 3 → F →L[ℝ] G)
    (zH : E →L[ℝ] E) (zL : F →L[ℝ] F)
    (CS : E →L[ℝ] F) (GP : F →L[ℝ] F)
    (KN : Fin 3 → E →L[ℝ] F) (GN : Fin 3 → F →L[ℝ] F)
    (hA : ∀ x, J (AH x)=AL (I x))
    (hP : ∀ x, J (PL x)=PN (J x))
    (hN : ∀ m x, J (NL m x)=NN m (J x))
    (hCS : ∀ x, J (CS x)=AL (SH x)-SL (AH x))
    (hGP : ∀ x, J (GP x)=AL (PL x)-PN (AL x))
    (hKN : ∀ m x, J (KN m x)=aL m (AH x)-AL (aH m x))
    (hGN : ∀ m x, J (GN m x)=AL (NL m x)-NN m (AL x)) (x : E) :
    J (GP (SH x)+PL (CS x)+
      (∑ m : Fin 3, (GN m (aH m x)-NL m (KN m x)))+
        AH (zH x)-zL (AH x)) =
      AL (PL (SH x)+(∑ m : Fin 3, NL m (aH m x))+I (zH x))-
        (PN (SL (AH x))+(∑ m : Fin 3, NN m (aL m (AH x)))+J (zL (AH x))) := by
  simp only [map_add,map_sub,map_sum,hGP,hP,hCS,hGN,hN,hKN,hA,Finset.sum_sub_distrib]
  abel
end Algebra

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

/-- All bands of the original lowering/E gain, with the caller's retained coefficient germs. -/
def loweringEHigh (hreg : FixedDirichletRegularity)
    (G : Fin 3 → Pphys → Half →L[ℝ] Half) (δ0 : ℝ) (W : CoeffRoom δ0)
    (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (CT hreg G i t.1).comp (PiH j t)+(TH t.1).comp (LH δ0 W i (Sum.inl j) t)+
    (∑ m : Fin 3, ((KK i m).comp (NH (NJ3 j m t.1))+
      (AH m).comp (LH δ0 W i (Sum.inr (j,m)) t)))+
    (aH i).comp (ZH j t.1)-(ZL j t.1).comp (aH i)

/-- The original raising/ordered-reverse gain, preserving the negative canonical bracket sign. -/
def raisingReverseHigh (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (RA δ0 W i (Sum.inl j) t).comp (SH t.1.1 t.1.2.1 t.1.2.2)+
    (PiL j t).comp (CS hreg i t.1.1 t.1.2.1 t.1.2.2)+
    (∑ m : Fin 3, ((RA δ0 W i (Sum.inr (j,m)) t).comp (aH m)-
      (NL (NJ2 j m t.1)).comp (KK m i)))+
    (AH i).comp (zH j t.1)-(zL j t.1).comp (AH i)
local notation "CH" => loweringEHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "HH" => raisingReverseHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  zeroCorrectionHigh zeroCorrectionHalf zeroReverseHigh zeroReverseHalf
  originalRadialReverseHigh originalRadialReverseLow jacobiAngularReverseHigh jacobiAngularReverseLow
  loweringHigh loweringLow raisingHigh raisingLow retainedJets
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL loweringMultiplierHigh raisingMultiplierHalf
  loweringEHigh raisingReverseHigh

/-- The complete lowering/E graph at an actual retained point. The room producer below discharges its word inputs. -/
lemma loweringEHigh_graph_of_actual_words
    (hreg : FixedDirichletRegularity) (G : Fin 3 → Pphys → Half →L[ℝ] Half)
    (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hCT : ∀ x : Hi, JL (CT hreg G i t.1 x)=aL i (TH t.1 x)-TL t.1 (aH i x))
    (hM : ∀ c : RetainedCoefficient, ∀ x : Hi,
      IH (LH δ0 W i c t x)=aH i (NH (QW δ0 W c t) x)-
        NL (smoothMultiplierLowerJets (QW δ0 W c t)) (aH i x))
    (u : Hi) : JL (CH hreg G δ0 W i j t u)=aL i (EH j t u)-EL j t (aH i u) := by
  have hT (x : Hi) : JL (TH t.1 x)=TL t.1 (IH x) :=
    v016_actual_Th_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg x
  have hPi := (W.piGerm j t ht).self_of_nhds
  have hGP (x : Hi) := hM (Sum.inl j) x
  simp only [retainedJets,piJets,hPi.1,hPi.2.1] at hGP
  have hN (m : Fin 3) := (W.jacobiGerm j m t.1 ht.1).self_of_nhds
  have hGN (m : Fin 3) (x : Hi) :
      IH (LH δ0 W i (Sum.inr (j,m)) t x)=
        aH i (NH (NJ3 j m t.1) x)-NL (NJ2 j m t.1) (aH i x) := by
    simpa only [retainedJets,jacobiJets,(hN m).1,(hN m).2.1] using hM (Sum.inr (j,m)) x
  have hFull := lowering_forward_assembly IH JL (aH i) (aL i) (TH t.1) (TL t.1)
    (PiH j t) (PiL j t) (fun m => NH (NJ3 j m t.1)) (fun m => NL (NJ2 j m t.1)) AH AL
    (ZH j t.1) (ZL j t.1) (CT hreg G i t.1) (LH δ0 W i (Sum.inl j) t)
    (fun m => KK i m) (fun m => LH δ0 W i (Sum.inr (j,m)) t)
    (v017_inclusion_loweringHigh hF hO hD i) hT (v017_inclusion_raisingHigh hF hO hD)
    hCT hGP (gainedHigh_graph hF hO hD i) hGN u
  simpa only [loweringEHigh,canonicalHigh,canonicalLow,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
    using hFull

/-- Complete raising/ordered-reverse graph, with the exact negative canonical bracket. -/
lemma raisingReverseHigh_graph_of_actual_words
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hCS : ∀ x : Hi, JL (CS hreg i t.1.1 t.1.2.1 t.1.2.2 x)=
      AL i (SH t.1.1 t.1.2.1 t.1.2.2 x)-SL t.1.1 t.1.2.1 t.1.2.2 (AH i x))
    (hM : ∀ c : RetainedCoefficient, ∀ x : Half,
      JL (RA δ0 W i c t x)=AL i (NL (smoothMultiplierLowerJets (QW δ0 W c t)) x)-
        NN (smoothMultiplierLowerJets (QW δ0 W c t)) (AL i x))
    (u : Hi) : JL (HH hreg δ0 W i j t u)=AL i (eH j t u)-eL j t (AH i u) := by
  have hPi := (W.piGerm j t ht).self_of_nhds
  have hGP (x : Half) := hM (Sum.inl j) x
  simp only [retainedJets,piJets,hPi.2.1,hPi.2.2] at hGP
  have hN (m : Fin 3) := (W.jacobiGerm j m t.1 ht.1).self_of_nhds
  have hGN (m : Fin 3) (x : Half) :
      JL (RA δ0 W i (Sum.inr (j,m)) t x)=
        AL i (NL (NJ2 j m t.1) x)-NN (NJ2 j m t.1) (AL i x) := by
    simpa only [retainedJets,jacobiJets,(hN m).2.1,(hN m).2.2] using hM (Sum.inr (j,m)) x
  have hP (v : Half) : JL (PiL j t v)=PiN j t (JL v) := by
    have he := v017_native_half_negative hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t)) v
    simpa only [piJets,hPi.2.1,hPi.2.2] using he
  have hNN (m : Fin 3) (v : Half) :
      JL (NL (NJ2 j m t.1) v)=NN (NJ2 j m t.1) (JL v) :=
    v017_native_half_negative hcalc hF hO hD τ0 (NJ2 j m t.1) v
  have hFull := raising_reverse_assembly IH JL (AH i) (AL i)
    (SH t.1.1 t.1.2.1 t.1.2.2) (SL t.1.1 t.1.2.1 t.1.2.2)
    (PiL j t) (PiN j t) (fun m => NL (NJ2 j m t.1)) (fun m => NN (NJ2 j m t.1))
    aH aL (zH j t.1) (zL j t.1) (CS hreg i t.1.1 t.1.2.1 t.1.2.2)
    (RA δ0 W i (Sum.inl j) t) (fun m => KK m i)
    (fun m => RA δ0 W i (Sum.inr (j,m)) t)
    (v017_inclusion_raisingHigh hF hO hD i) hP hNN hCS hGP
    (fun m => gainedHigh_graph hF hO hD m i) hGN u
  simpa only [raisingReverseHigh,orderedReverseHigh,orderedReverseLow,
    originalRadialReverseHigh,originalRadialReverseLow,jacobiAngularReverseHigh,jacobiAngularReverseLow,
    sharpRemainder,lowerSharpRemainder,referenceSharpRadialTraceSecondRemainder,referenceLowerRadialTraceSecondRemainder,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply] using hFull

private lemma retain_lowering_room {D V I : Type*}
    {A B C : D → Prop} {P Q : D → V → Prop} {R S T : D → V → I → Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ v : V,
      P d v ∧ Q d v ∧ ∀ i, R d v i ∧ S d v i ∧ T d v i) :
    ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ v : V, ∀ i, R d v i := by
  rcases h with ⟨d,ha,hb,hc,v,_hp,_hq,hr⟩
  exact ⟨d,ha,hb,hc,v,fun i => (hr i).1⟩

private lemma retain_mixed_room {D K : Type*}
    {A B C S G : D → Prop} {P N : D → K → Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ k : K, P d k ∧ S d ∧ G d ∧ N d k) :
    ∃ d : D, A d ∧ G d := by
  rcases h with ⟨d,ha,_hb,_hc,_k,_hp,_hs,hg,_hn⟩
  exact ⟨d,ha,hg⟩

private lemma use_three_graph_rooms {D U V W : Type*}
    {A B C : D → Prop} {Q : D → W → Prop}
    {P G : U → Prop} {E F H : V → Prop} {Result : Prop}
    (ht : ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ w : W, Q d w)
    (hm : ∃ u : U, P u ∧ G u) (hs : ∃ v : V, E v ∧ F v ∧ H v)
    (use : ∀ d u v w, A d → B d → C d → Q d w → P u → G u →
      E v → F v → H v → Result) : Result := by
  rcases ht with ⟨d,ha,hb,hc,w,hq⟩
  rcases hm with ⟨u,hp,hg⟩
  rcases hs with ⟨v,he,hf,hh⟩
  exact use d u v w ha hb hc hq hp hg he hf hh

include hg in
/-- Actual lowering/T graph room; all unused derivative bounds stay in its native receipt. -/
lemma exists_loweringT_graph_room (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ commonRoom y0 ρ d ⊆ Ω ∧
      ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
        ∀ i : Fin 3, ∀ p ∈ commonRoom y0 ρ d, ∀ u : Hi,
          JL (CT hreg G i p u)=aL i (TH p u)-TL p (aH i u) := by
  exact retain_lowering_room
    (exists_reference_commonRadius_loweringAngularHigh_graph_caps
      hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel)

/-- Both actual retained coefficient graphs on one caller-owned room. -/
lemma exists_mixedMultiplier_graph_room (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ d : ℝ, 0 < d ∧ ∀ i : Fin 3, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom d,
      (∀ u : Hi, IH (LH δ0 W i c t u)=aH i (NH (QW δ0 W c t) u)-
        NL (smoothMultiplierLowerJets (QW δ0 W c t)) (aH i u)) ∧
      (∀ v : Half, JL (RA δ0 W i c t v)=AL i (NL (smoothMultiplierLowerJets (QW δ0 W c t)) v)-
        NN (smoothMultiplierLowerJets (QW δ0 W c t)) (AL i v)) := by
  exact retain_mixed_room
    (exists_commonRoom_actual_mixed_multiplier_gains
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg hKernel δ0 hδ0 W)

/-- One actual common room for BOTH full mixed high graphs. No word graph callback remains. -/
theorem exists_commonRoom_actual_mixedAngular_high_graphs
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
      ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
        ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
          (∀ u : Hi, JL (CH hreg G δ0 W i j t u)=aL i (EH j t u)-EL j t (aH i u)) ∧
          (∀ u : Hi, JL (HH hreg δ0 W i j t u)=AL i (eH j t u)-eL j t (AH i u)) := by
  apply use_three_graph_rooms
    (exists_loweringT_graph_room hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg hKernel)
    (exists_mixedMultiplier_graph_room hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg hKernel δ0 hδ0 W)
    (exists_reference_commonRadius_highSmoothMultiplierSecondRemainder_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel)
  intro dT dM dS G hdT hdTρ hRoomT hCT hdM hMG hdS _hdSρ hSharp
  let δ : ℝ := min δ0 (min dT (min dM dS))
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdT (lt_min hdM hdS))
  have hδ0le : δ ≤ δ0 := min_le_left _ _
  have hδT : δ ≤ dT := (min_le_right _ _).trans (min_le_left _ _)
  have hδM : δ ≤ dM := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδS : δ ≤ dS := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hSub0 := commonRoom_mono y0 ρ hδ0le
  have hSubT := commonRoom_mono y0 ρ hδT
  have hSubM := commonRoom_mono y0 ρ hδM
  have hSubS := commonRoom_mono y0 ρ hδS
  refine ⟨δ,hδ,hδ0le,hδT.trans hdTρ,fun p hp => hRoomT (hSubT hp),G,?_⟩
  intro i j t ht
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    hRoomT t.1 (hSubT ht.1)
  have hSharpAt (k : Fin 3) (u : Hi) := hSharp t.1.1 ht.1.1 t.1.2.1
    (by simpa only [mem_closedBall,dist_eq_norm] using ht.1.2.1)
    t.1.2.2 (abs_le.mpr (hSubS ht.1).2.2) (coordinateJets k) u
  have hCS (u : Hi) : JL (CS hreg i t.1.1 t.1.2.1 t.1.2.2 u)=
      AL i (SH t.1.1 t.1.2.1 t.1.2.2 u)-SL t.1.1 t.1.2.1 t.1.2.2 (AH i u) := by
    simpa only [raisingHigh,raisingLow] using
      raisingAngularHighCommutator_graph_of_sharpMultiplierGraph
        hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg i
          t.1.1 t.1.2.1 t.1.2.2 hSeg hSharpAt u
  exact ⟨loweringEHigh_graph_of_actual_words hF hO hD hcalc τ0
      g L y0 Φ B ε C ρ H a w hData hg hreg G δ0 W i j t ⟨hSub0 ht.1,ht.2⟩ hSeg
        (hCT i t.1 (hSubT ht.1)) (fun c => (hMG i c t ⟨hSubM ht.1,ht.2⟩).1),
    raisingReverseHigh_graph_of_actual_words hF hO hD hcalc τ0
      g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W i j t ⟨hSub0 ht.1,ht.2⟩ hCS
        (fun c => (hMG i c t ⟨hSubM ht.1,ht.2⟩).2)⟩

/-- The signed adjoint partner is the NEGATIVE raising/reverse gain, at the same i,j. -/
lemma mixed_high_pairing_of_graphs
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (Cf Hf : Hi →L[ℝ] Half)
    (hC : ∀ u : Hi, JL (Cf u)=aL i (EH j t u)-EL j t (aH i u))
    (hH : ∀ u : Hi, JL (Hf u)=AL i (eH j t u)-eL j t (AH i u))
    (u v : Hi) : PP (IH v) (JL (Cf u))=PP (IH u) (JL ((-Hf) v)) := by
  have hForwardCompat (z : Hi) : JL (EH j t z)=EL j t (IH z) := by
    have hp := (W.piGerm j t ht).self_of_nhds
    exact canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg j t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t)
      hp.1 hp.2.1 z
  have hReverseCompat (z : Hi) : JL (eH j t z)=eL j t (IH z) := by
    have hp := (W.piGerm j t ht).self_of_nhds
    simpa only [orderedReverseHigh,orderedReverseLow,originalRadialReverseHigh,
      originalRadialReverseLow,jacobiAngularReverseHigh,jacobiAngularReverseLow] using
      explicit_ordered_reverse_high_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        j t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t)
        hp.2.1 hp.2.2 z
  have hPivot (x y : Half) : PP x (EL j t y)=PP y (eL j t x) := by
    have hp := (W.piGerm j t ht).self_of_nhds
    simpa only [orderedReverseLow,originalRadialReverseLow,jacobiAngularReverseLow] using
      canonicalLow_explicit_ordered_reverse_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        j t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t)
        hp.2.1 hp.2.2 x y
  have hForward (z : Hi) (x : Half) : PP (IH z) (EL j t x)=PP x (JL (eH j t z)) :=
    (hPivot (IH z) x).trans (congrArg (PP x) (hReverseCompat z).symm)
  have hReverse (z : Hi) (x : Half) : PP (IH z) (eL j t x)=PP x (JL (EH j t z)) :=
    (hPivot x (IH z)).symm.trans (congrArg (PP x) (hForwardCompat z).symm)
  have h1 : PP (IH v) (aL i (EH j t u))=PP (IH u) (eL j t (AH i v)) :=
    (v017_aA1 hF hO hD i v (EH j t u)).trans
      ((v016_pairing_inclusion_symm (EH j t u) (AH i v)).trans
        (hReverse u (AH i v)).symm)
  have h2 : PP (IH v) (EL j t (aH i u))=PP (IH u) (AL i (eH j t v)) :=
    (hForward v (aH i u)).trans (v017_aA2 hF hO hD i u (eH j t v))
  have hD : JL ((-Hf) v)=eL j t (AH i v)-AL i (eH j t v) := by
    simp only [ContinuousLinearMap.neg_apply,map_neg,hH]
    abel
  have hc := (congrArg (fun z : Neg => PP (IH v) z) (hC u)).trans
    (v016_pairing_sub_right (IH v) _ _)
  have hd := (congrArg (fun z : Neg => PP (IH u) z) hD).trans
    (v016_pairing_sub_right (IH u) _ _)
  exact hc.trans ((congrArg₂ (fun x y : ℝ => x-y) h1 h2).trans hd.symm)

private lemma balanced_low_exists (Cf Df : Hi →L[ℝ] Half)
    (hAdj : ∀ u v : Hi, PP (IH v) (JL (Cf u))=PP (IH u) (JL (Df v))) :
    ∃ Bf : Half →L[ℝ] Neg,
      Bf.comp IH=(JL).comp Cf ∧
      (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp Bf=
        (v016TransposeL Df).comp JL ∧ ‖Bf‖ ≤ (‖Df‖+‖Cf‖)/2 := by
  have hc := v016_compatible_of_adjunction Cf Df hAdj
  let Bf : Half →L[ℝ] Neg := sphereSobolevBalancedDualEndpointL (v016TransposeL Df) Cf hc
  have hU : Bf.comp IH=(JL).comp Cf :=
    sphereSobolevBalancedDualEndpointL_upper_inclusion (v016TransposeL Df) Cf hc
  have hL : (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp Bf=
      (v016TransposeL Df).comp JL :=
    sphereSobolevBalancedDualEndpointL_lower_inclusion (v016TransposeL Df) Cf hc
  have hN := norm_sphereSobolevBalancedDualEndpointL_le (v016TransposeL Df) Cf hc
  have hNT := norm_v016TransposeL_apply_le Df
  exact ⟨Bf,hU,hL,hN.trans (by linarith)⟩

private lemma use_high_graph_room {D G : Type*} {A B C K : D → Prop} {P : D → G → Prop}
    {Result : Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d ∧ K d ∧ ∃ g : G, P d g)
    (use : ∀ d g, A d → B d → C d → K d → P d g → Result) : Result := by
  rcases h with ⟨d,ha,hb,hc,hk,g,hp⟩
  exact use d g ha hb hc hk hp

/-- Genuine balanced mixed angular endpoint on one actual room and one original W.
The low endpoint has BOTH inclusion identities and a cap by its two actual high parents.
Uniform derivative caps and the physical signed integral estimate are subsequent obligations. -/
theorem exists_commonRoom_actual_mixedAngular_paired_endpoints
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
      ∃ Bl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg,
        ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
          (∀ u : Hi, JL (CH hreg G δ0 W i j t u)=aL i (EH j t u)-EL j t (aH i u)) ∧
          (∀ u : Hi, JL (HH hreg δ0 W i j t u)=AL i (eH j t u)-eL j t (AH i u)) ∧
          (Bl i j t).comp IH=(JL).comp (CH hreg G δ0 W i j t) ∧
          (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Bl i j t)=
            (v016TransposeL (-(HH hreg δ0 W i j t))).comp JL ∧
          ‖Bl i j t‖ ≤ (‖HH hreg δ0 W i j t‖+‖CH hreg G δ0 W i j t‖)/2 := by
  classical
  apply use_high_graph_room
    (exists_commonRoom_actual_mixedAngular_high_graphs
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg hKernel δ0 hδ0 W)
  intro δ G hδ hδ0le hδρ hRoom hGraphs
  have hSub := commonRoom_mono y0 ρ hδ0le
  have hLow (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ∃ Bf : Half →L[ℝ] Neg,
        Bf.comp IH=(JL).comp (CH hreg G δ0 W i j t) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp Bf=
          (v016TransposeL (-(HH hreg δ0 W i j t))).comp JL ∧
        ‖Bf‖ ≤ (‖HH hreg δ0 W i j t‖+‖CH hreg G δ0 W i j t‖)/2 := by
    have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      hRoom t.1 ht.1
    have hAdj := mixed_high_pairing_of_graphs hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W i j t ⟨hSub ht.1,ht.2⟩ hSeg
      (CH hreg G δ0 W i j t) (HH hreg δ0 W i j t) (hGraphs i j t ht).1 (hGraphs i j t ht).2
    simpa only [ContinuousLinearMap.opNorm_neg] using balanced_low_exists
      (CH hreg G δ0 W i j t) (-(HH hreg δ0 W i j t)) hAdj
  let Bl (i j : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
    if ht : t ∈ ParamRoom δ then Classical.choose (hLow i j t ht) else 0
  refine ⟨δ,hδ,hδ0le,hδρ,G,Bl,?_⟩
  intro i j t ht
  have hAt := Classical.choose_spec (hLow i j t ht)
  have hBl : Bl i j t=Classical.choose (hLow i j t ht) := dif_pos ht
  exact ⟨(hGraphs i j t ht).1,(hGraphs i j t ht).2,by simpa only [hBl] using hAt⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
