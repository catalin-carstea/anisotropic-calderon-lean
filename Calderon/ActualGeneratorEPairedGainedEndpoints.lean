import Calderon.ActualGeneratorEHighGainedGraph
import Calderon.NativeRadialJetTranspose
import Calderon.SphereSobolevHalfDualRotationPairing
import Calderon.ActualHorizontalGeometry

/-! Source-only Sol author candidate. Exact upfront W-E-paired-before-v001.
Ordinary17612 and E/Ev003 dependencies are unqualified. Physical degree k,
true angular reverse, retained W, no independent derivative-gain premise. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEPairedGainedEndpoints
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
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

def generatorSharpHigh (V : Generator) : Hi →L[ℝ] Half :=
  match V with | Sum.inl _ => -generatorHigh V | Sum.inr _ => generatorHigh V
def generatorSharpLow (V : Generator) : Half →L[ℝ] Neg :=
  match V with | Sum.inl _ => -generatorLow V | Sum.inr _ => generatorLow V

private lemma generator_compat (V : Generator) (u : Hi) :
    JL (generatorHigh V u)=generatorLow V (IH u) := by
  cases V with
  | inl ij => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) (sphereSobolevRotationL_threehalf_half_compatibility ij.1 ij.2)
  | inr z => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) sphereSobolevShiftedDegree_high_half_compatibility
private lemma generatorSharp_compat (V : Generator) (u : Hi) :
    JL (generatorSharpHigh V u)=generatorSharpLow V (IH u) := by
  cases V with
  | inl ij => simpa only [generatorSharpHigh,generatorSharpLow,ContinuousLinearMap.neg_apply,map_neg] using
      congrArg (fun z : Neg => -z) (generator_compat (Sum.inl ij) u)
  | inr z => exact generator_compat (Sum.inr z) u

private lemma generator_low_pivots (V : Generator) (x y : Half) :
    PP x (generatorLow V y)=PP y (generatorSharpLow V x) ∧
    PP x (generatorSharpLow V y)=PP y (generatorLow V x) := by
  cases V with
  | inl ij =>
    have h := sphereSobolevDualPairing_half_rotation_skew ij.1 ij.2 y x
    have hFirst : PP x (sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 y)=
        -PP y (sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 x) :=
      (real_inner_comm x (sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 y)).symm.trans h
    constructor
    · simpa only [generatorLow,generatorSharpLow,ContinuousLinearMap.neg_apply,sphereSobolevDualPairing,inner_neg_right] using hFirst
    · change ⟪x,-sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 y⟫_ℝ =
        ⟪y,sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 x⟫_ℝ
      rw [inner_neg_right]
      change ⟪x,sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 y⟫_ℝ =
        -⟪y,sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 x⟫_ℝ at hFirst
      linarith
  | inr z =>
    have h := sphereSobolevDualPairing_lower_distributionalTranspose (sphereSobolevShiftedDegreeL (1/2 : ℝ)) y x
    rw [sphereLowerDistributionalTranspose_shiftedDegree_half] at h
    exact ⟨h,h⟩

section Algebra
variable {E F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N]
private lemma leftMultiplier_orderOne_graph
    (J : F →L[ℝ] N) (VH TH : E →L[ℝ] F) (VL TL : F →L[ℝ] N)
    (PL : F →L[ℝ] F) (PN : N →L[ℝ] N) (U : F →L[ℝ] F) (D : E →L[ℝ] F)
    (hU : ∀ v, J (U v)=VL (PL v)-PN (VL v))
    (hP : ∀ v, J (PL v)=PN (J v))
    (hD : ∀ u, J (D u)=VL (TH u)-TL (VH u)) (u : E) :
    J ((U.comp TH+PL.comp D) u)=VL (PL (TH u))-PN (TL (VH u)) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add,hU,hP,hD,map_sub]
  abel
/-- Finite literal reverse row assembly, with operator values kept abstract. -/
private lemma finiteReverseRow_graph
    (I : E →L[ℝ] F) (J : F →L[ℝ] N)
    (VH TH : E →L[ℝ] F) (VL TL : F →L[ℝ] N)
    (PL : F →L[ℝ] F) (PN : N →L[ℝ] N)
    (AL : Fin 3 → F →L[ℝ] F) (AN : Fin 3 → N →L[ℝ] N)
    (AH : Fin 3 → E →L[ℝ] F) (Alow : Fin 3 → F →L[ℝ] N)
    (ZH : E →L[ℝ] E) (ZL : F →L[ℝ] F)
    (CR : E →L[ℝ] F) (CA : Fin 3 → E →L[ℝ] F) (u : E)
    (hR : J (CR u)=VL (PL (TH u))-PN (TL (VH u)))
    (hA : ∀ m, J (CA m u)=VL (AL m (AH m u))-AN m (Alow m (VH u)))
    (hZ : J (VH (ZH u))=VL (I (ZH u))) :
    J ((CR+∑ m : Fin 3,CA m+VH.comp ZH-ZL.comp VH) u)=
      VL (((PL.comp TH+∑ m : Fin 3,(AL m).comp (AH m))+(I).comp ZH) u)-
        ((PN.comp TL+∑ m : Fin 3,(AN m).comp (Alow m))+(J).comp ZL) (VH u) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_add,map_sub,map_sum,
    hR,hA,hZ,Finset.sum_sub_distrib]
  abel

private lemma negative_difference_value (x y z : N) (h : x=y-z) : -x = -y+z := by
  rw [h]
  abel

private lemma negative_difference_swap (x y z : N) (h : x=y-z) : -x = z-y := by
  rw [h]
  abel

end Algebra

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
local notation "UH" => retainedGeneratorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UL" => retainedGeneratorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CGE" => generatorEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "CT" => generatorAdjointRadialHigh g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "CS" => generatorSharpRadialHigh g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sh" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sl" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

def reverseEHigh (j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (PiL j t).comp (Sh t.1)+(∑ m : Fin 3,(NL (NJ2 j m t.1)).comp (loweringHigh hF hO hD m))+(IH).comp (zH j t.1)
def reverseELow (j : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  (PiN j t).comp (Sl t.1)+(∑ m : Fin 3,(NN (NJ2 j m t.1)).comp (loweringLow hF hO hD m))+(JL).comp (zL j t.1)
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def generatorLoweringHigh (V : Generator) (m : Fin 3) : Hi →L[ℝ] Half :=
  match V with | Sum.inl ij => rotationLoweringHigh hF hO hD ij.1 ij.2 m | Sum.inr _ => -loweringHigh hF hO hD m
private lemma generatorLoweringHigh_graph (V : Generator) (m : Fin 3) (u : Hi) :
    JL (generatorLoweringHigh hF hO hD V m u)=generatorLow V (loweringHigh hF hO hD m u)-loweringLow hF hO hD m (generatorHigh V u) := by
  cases V with
  | inl ij => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) (rotationLoweringHigh_graph hF hO hD ij.1 ij.2 m)
  | inr z => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) (degreeLoweringHigh_graph hF hO hD m)

/-- Complete actual [V,e_j] high gain, the genuine reverse-E word. -/
def generatorReverseEHigh (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (V : Generator) (j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (UL δ0 W V (Sum.inl j) t).comp (Sh t.1)+(NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t))).comp (CS hreg V t.1)+
  (∑ m : Fin 3, ((UL δ0 W V (Sum.inr (j,m)) t).comp (loweringHigh hF hO hD m)+
    (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t))).comp (generatorLoweringHigh hF hO hD V m)))+
  (generatorHigh V).comp (zH j t.1)-(zL j t.1).comp (generatorHigh V)
local notation "DGE" => generatorReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def pairedLeftHigh (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (V : Generator) (j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  match V with | Sum.inl _ => -CGE hreg δ0 W V j t | Sum.inr _ => CGE hreg δ0 W V j t
def pairedRightHigh (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (V : Generator) (j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  -DGE hreg δ0 W V j t
local notation "CH" => pairedLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DH" => pairedRightHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

section ReverseGraph
attribute [local irreducible] generatorHigh generatorLow loweringHigh loweringLow
  sphereSobolevInclusionL retainedGeneratorHigh retainedGeneratorHalf
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sharpRemainder lowerSharpRemainder referencePiHalfMultiplier referencePiNegativeHalfMultiplier

private theorem generatorReverseEHigh_graph_at
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (V : Generator) (j : Fin 3) (t : Tpar)
    (ht : t ∈ ParamRoom δ0)
    (hS : ∀ u : Hi, JL (CS hreg V t.1 u)=generatorLow V (Sh t.1 u)-Sl t.1 (generatorHigh V u))
    (hU : ∀ c : RetainedCoefficient, ∀ v : Half, JL (UL δ0 W V c t v)=
      generatorLow V (NL (smoothMultiplierLowerJets (QW δ0 W c t)) v)-NN (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorLow V v)) (u : Hi) :
    JL (DGE hreg δ0 W V j t u)=generatorLow V (eH j t u)-eL j t (generatorHigh V u) := by
  have hp := (W.piGerm j t ht).self_of_nhds
  have hR0 := leftMultiplier_orderOne_graph JL (generatorHigh V) (Sh t.1) (generatorLow V) (Sl t.1)
    (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t))) (NN (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t)))
    (UL δ0 W V (Sum.inl j) t) (CS hreg V t.1) (hU (Sum.inl j))
    (v017_native_half_negative hcalc hF hO hD τ0 (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t))) hS u
  have hR : JL (((UL δ0 W V (Sum.inl j) t).comp (Sh t.1)+
      (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t))).comp (CS hreg V t.1)) u)=
      generatorLow V (PiL j t (Sh t.1 u))-PiN j t (Sl t.1 (generatorHigh V u)) := by
    simpa only [retainedJets,piJets,hp.2.1,hp.2.2] using hR0
  have hA (m : Fin 3) : JL (((UL δ0 W V (Sum.inr (j,m)) t).comp (loweringHigh hF hO hD m)+
      (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t))).comp (generatorLoweringHigh hF hO hD V m)) u)=
      generatorLow V (NL (NJ2 j m t.1) (loweringHigh hF hO hD m u))-
        NN (NJ2 j m t.1) (loweringLow hF hO hD m (generatorHigh V u)) := by
    have hNative := leftMultiplier_orderOne_graph JL (generatorHigh V) (loweringHigh hF hO hD m)
      (generatorLow V) (loweringLow hF hO hD m)
      (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t))) (NN (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t)))
      (UL δ0 W V (Sum.inr (j,m)) t) (generatorLoweringHigh hF hO hD V m) (hU (Sum.inr (j,m)))
      (v017_native_half_negative hcalc hF hO hD τ0 (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t)))
      (generatorLoweringHigh_graph hF hO hD V m) u
    have hn := (W.jacobiGerm j m t.1 ht.1).self_of_nhds
    simpa only [retainedJets,jacobiJets,hn.2.1,hn.2.2] using hNative
  have hZero := generator_compat V (zH j t.1 u)
  have hFull := finiteReverseRow_graph IH JL (generatorHigh V) (Sh t.1) (generatorLow V) (Sl t.1)
    (PiL j t) (PiN j t) (fun m => NL (NJ2 j m t.1)) (fun m => NN (NJ2 j m t.1))
    (fun m => loweringHigh hF hO hD m) (fun m => loweringLow hF hO hD m)
    (zH j t.1) (zL j t.1)
    ((UL δ0 W V (Sum.inl j) t).comp (Sh t.1)+
      (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t))).comp (CS hreg V t.1))
    (fun m => (UL δ0 W V (Sum.inr (j,m)) t).comp (loweringHigh hF hO hD m)+
      (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t))).comp
        (generatorLoweringHigh hF hO hD V m)) u hR hA hZero
  simpa only [generatorReverseEHigh,reverseEHigh,reverseELow] using hFull

end ReverseGraph

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
      simpa only [jacobiJets,smoothMultiplierLowerJets_commonSupport] using
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
  refine ⟨?_,?_,?_,?_⟩
  · unfold zeroCorrectionHigh
    exact hr.smul (ContDiffOn.sum (fun m _ => (hDr (3/2 : ℝ)).clm_comp (contDiffOn_const.clm_comp (hNH m))))
  · unfold zeroCorrectionHalf
    exact hr.smul (ContDiffOn.sum (fun m _ => (hDr (1/2 : ℝ)).clm_comp (contDiffOn_const.clm_comp (hNL m))))
  · unfold zeroReverseHigh
    exact hr.smul (ContDiffOn.sum (fun m _ => (hNH m).clm_comp (contDiffOn_const.clm_comp (hdr (3/2 : ℝ)))))
  · unfold zeroReverseHalf
    exact hr.smul (ContDiffOn.sum (fun m _ => (hNL m).clm_comp (contDiffOn_const.clm_comp (hdr (1/2 : ℝ)))))

private lemma generator_E_both_smooth
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0) (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (hU : ∀ V : Generator, ∀ c : RetainedCoefficient,
      ContDiffOn ℝ ∞ (UH δ0 W V c) (ParamRoom δ) ∧ ContDiffOn ℝ ∞ (UL δ0 W V c) (ParamRoom δ))
    (hR : ∀ V : Generator, ContDiffOn ℝ ∞ (CT hreg V) (commonRoom y0 ρ δ) ∧ ContDiffOn ℝ ∞ (CS hreg V) (commonRoom y0 ρ δ))
    (V : Generator) (j : Fin 3) :
    ContDiffOn ℝ ∞ (CGE hreg δ0 W V j) (ParamRoom δ) ∧ ContDiffOn ℝ ∞ (DGE hreg δ0 W V j) (ParamRoom δ) := by
  have hProj : MapsTo (Prod.fst : Tpar → Pphys) (ParamRoom δ) (commonRoom y0 ρ δ) := fun t ht => ht.1
  have hCT := (hR V).1.comp contDiffOn_fst hProj
  have hCS := (hR V).2.comp contDiffOn_fst hProj
  have hQ (c : RetainedCoefficient) := retainedNative_contDiff g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W c
  have hQH (c : RetainedCoefficient) : ContDiffOn ℝ ∞ (fun t => NH (QW δ0 W c t)) (ParamRoom δ) := (hQ c).1.contDiffOn
  have hQL (c : RetainedCoefficient) : ContDiffOn ℝ ∞ (fun t => NL (smoothMultiplierLowerJets (QW δ0 W c t))) (ParamRoom δ) := (hQ c).2.contDiffOn
  have hZ := zeroFamilies_contDiffOn g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W δ hSub j
  have hRem (t : Tpar) (ht : t ∈ ParamRoom δ) := contDiffAt_actualAngularRadialRemainder_families_of_segment
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1
    (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1)
  have hTh : ContDiffOn ℝ ∞ (fun t : Tpar => Th t.1) (ParamRoom δ) := fun t ht =>
    ((hRem t ht).1.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  have hSh : ContDiffOn ℝ ∞ (fun t : Tpar => Sh t.1) (ParamRoom δ) := fun t ht =>
    ((hRem t ht).2.2.1.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  refine ⟨?_,?_⟩
  · unfold generatorEHigh
    exact ((((hCT.clm_comp (hQH (Sum.inl j))).add (hTh.clm_comp (hU V (Sum.inl j)).1)).add
      (ContDiffOn.sum (fun m _ => (contDiffOn_const.clm_comp (hQH (Sum.inr (j,m)))).add
        (contDiffOn_const.clm_comp ((hU V (Sum.inr (j,m))).1))))).add
      (contDiffOn_const.clm_comp hZ.1)).sub (hZ.2.1.clm_comp contDiffOn_const)
  · unfold generatorReverseEHigh
    exact (((((hU V (Sum.inl j)).2.clm_comp hSh).add
      ((hQL (Sum.inl j)).clm_comp hCS)).add
      (ContDiffOn.sum (fun m _ => ((hU V (Sum.inr (j,m))).2.clm_comp contDiffOn_const).add
        ((hQL (Sum.inr (j,m))).clm_comp contDiffOn_const)))).add
      (contDiffOn_const.clm_comp hZ.2.2.1)).sub (hZ.2.2.2.clm_comp contDiffOn_const)

section PairingGraphs
attribute [local irreducible] canonicalHigh canonicalLow reverseEHigh reverseELow
  generatorHigh generatorLow generatorEHigh generatorReverseEHigh
  sphereSobolevInclusionL sphereSobolevDualPairing

private theorem actual_generator_E_paired_adjunction
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (V : Generator) (j : Fin 3) (t : Tpar)
    (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hC : ∀ u, JL (CH hreg δ0 W V j t u)=generatorSharpLow V (EH j t u)-EL j t (generatorSharpHigh V u))
    (hPartner : ∀ u, JL (DH hreg δ0 W V j t u)=eL j t (generatorHigh V u)-generatorLow V (eH j t u))
    (u v : Hi) : PP (IH v) (JL (CH hreg δ0 W V j t u))=PP (IH u) (JL (DH hreg δ0 W V j t v)) := by
  have hp := (W.piGerm j t ht).self_of_nhds
  let Q := piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t
  have hEC (z : Hi) := canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg j t hSeg Q hp.1 hp.2.1 z
  have heC (z : Hi) : JL (eH j t z)=eL j t (IH z) := by
    simpa only [reverseEHigh,reverseELow] using explicit_ordered_reverse_high_low_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t hSeg Q hp.2.1 hp.2.2 z
  have hP (x y : Half) : PP x (EL j t y)=PP y (eL j t x) := by
    simpa only [reverseELow] using canonicalLow_explicit_ordered_reverse_pairing
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t hSeg Q hp.2.1 hp.2.2 x y
  have hForward (z : Hi) (x : Half) : PP (IH z) (EL j t x)=PP x (JL (eH j t z)) :=
    (hP (IH z) x).trans (congrArg (PP x) (heC z).symm)
  have hReverse (z : Hi) (x : Half) : PP (IH z) (eL j t x)=PP x (JL (EH j t z)) :=
    (hP x (IH z)).symm.trans (congrArg (PP x) (hEC z).symm)
  have hVF (z : Hi) (x : Half) : PP (IH z) (generatorLow V x)=PP x (JL (generatorSharpHigh V z)) :=
    (generator_low_pivots V (IH z) x).1.trans (congrArg (PP x) (generatorSharp_compat V z).symm)
  have hVR (z : Hi) (x : Half) : PP (IH z) (generatorSharpLow V x)=PP x (JL (generatorHigh V z)) :=
    (generator_low_pivots V (IH z) x).2.trans (congrArg (PP x) (generator_compat V z).symm)
  have h1 : PP (IH v) (generatorSharpLow V (EH j t u))=PP (IH u) (eL j t (generatorHigh V v)) :=
    (hVR v (EH j t u)).trans ((v016_pairing_inclusion_symm (EH j t u) (generatorHigh V v)).trans
      (hReverse u (generatorHigh V v)).symm)
  have h2 : PP (IH v) (EL j t (generatorSharpHigh V u))=PP (IH u) (generatorLow V (eH j t v)) :=
    (hForward v (generatorSharpHigh V u)).trans ((v016_pairing_inclusion_symm (generatorSharpHigh V u) (eH j t v)).trans
      (hVF u (eH j t v)).symm)
  have hc := (congrArg (fun z : Neg => PP (IH v) z) (hC u)).trans (v016_pairing_sub_right (IH v) _ _)
  have hd := (congrArg (fun z : Neg => PP (IH u) z) (hPartner v)).trans (v016_pairing_sub_right (IH u) _ _)
  exact hc.trans ((congrArg₂ (fun x y : ℝ => x-y) h1 h2).trans hd.symm)

private lemma pairedHigh_graphs_at
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (V : Generator) (j : Fin 3) (t : Tpar)
    (hC : ∀ u, JL (CGE hreg δ0 W V j t u)=generatorLow V (EH j t u)-EL j t (generatorHigh V u))
    (hReverseGraph : ∀ u, JL (DGE hreg δ0 W V j t u)=generatorLow V (eH j t u)-eL j t (generatorHigh V u)) (u : Hi) :
    JL (CH hreg δ0 W V j t u)=generatorSharpLow V (EH j t u)-EL j t (generatorSharpHigh V u) ∧
    JL (DH hreg δ0 W V j t u)=eL j t (generatorHigh V u)-generatorLow V (eH j t u) := by
  refine ⟨?_,?_⟩
  · cases V with
    | inl ij =>
      simpa only [pairedLeftHigh,generatorSharpLow,generatorSharpHigh,ContinuousLinearMap.neg_apply,
        map_neg,sub_neg_eq_add] using negative_difference_value _ _ _ (hC u)
    | inr z => exact hC u
  · simpa only [pairedRightHigh,ContinuousLinearMap.neg_apply,map_neg] using
      negative_difference_swap _ _ _ (hReverseGraph u)

end PairingGraphs

/-- Concrete actual paired-generator endpoint data. The producer below proves
all fields from actual APIs; this record is not an external callback premise. -/
structure GeneratorEndpointRoom (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) where
  low : Generator → Fin 3 → Tpar → Half →L[ℝ] Neg
  smoothLeft : ∀ V j, ContDiffOn ℝ ∞ (CH hreg δ0 W V j) (ParamRoom δ)
  smoothRight : ∀ V j, ContDiffOn ℝ ∞ (DH hreg δ0 W V j) (ParamRoom δ)
  smoothLow : ∀ V j, ContDiffOn ℝ ∞ (low V j) (ParamRoom δ)
  highGraph : ∀ V j t, t ∈ ParamRoom δ → ∀ u : Hi,
    JL (CH hreg δ0 W V j t u)=generatorSharpLow V (EH j t u)-EL j t (generatorSharpHigh V u)
  partnerGraph : ∀ V j t, t ∈ ParamRoom δ → ∀ u : Hi,
    JL (DH hreg δ0 W V j t u)=eL j t (generatorHigh V u)-generatorLow V (eH j t u)
  adjunction : ∀ V j t, t ∈ ParamRoom δ → ∀ u v : Hi,
    PP (IH v) (JL (CH hreg δ0 W V j t u))=PP (IH u) (JL (DH hreg δ0 W V j t v))
  upper : ∀ V j t, t ∈ ParamRoom δ → (low V j t).comp IH=(JL).comp (CH hreg δ0 W V j t)
  lower : ∀ V j t, t ∈ ParamRoom δ → (I33).comp (low V j t)=(v016TransposeL (DH hreg δ0 W V j t)).comp JL
  midpoint : ∀ V j t, t ∈ ParamRoom δ → ‖low V j t‖ ≤ (‖DH hreg δ0 W V j t‖+‖CH hreg δ0 W V j t‖)/2
  finiteCaps : ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ V j, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ,
    ‖iteratedFDerivWithin ℝ n (CH hreg δ0 W V j) (ParamRoom δ) t‖ ≤ M ∧
    ‖iteratedFDerivWithin ℝ n (DH hreg δ0 W V j) (ParamRoom δ) t‖ ≤ M ∧
    ‖iteratedFDerivWithin ℝ n (low V j) (ParamRoom δ) t‖ ≤ M
local notation "GenRoom" => GeneratorEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Genuine full generator/E paired endpoint producer on ANY retained original
W, with total joint smoothness and every finite common joint cap. -/
theorem exists_retained_generator_paired_endpoints
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧ Nonempty (GenRoom hreg δ0 W δ) := by
  classical
  obtain ⟨dU,hdU,_hdU0,hdUρ,hUS,hUG,_hUC⟩ :=
    exists_commonRoom_retained_generator_multiplier_gains g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel δ0 hδ0 W
  obtain ⟨dR,hdR,_hdRρ,hRoomR,hRS,hRG,_hRC⟩ :=
    exists_commonRoom_actual_generator_radial_high_gains g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  obtain ⟨dC,hdC,_hdC0,_hdCρ,hCG⟩ := exists_commonRoom_actual_generator_E_high_graphs
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg hKernel δ0 hδ0 W
  let δ := min δ0 (min dU (min dR dC))
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdU (lt_min hdR hdC))
  have hδ0le : δ ≤ δ0 := min_le_left _ _
  have hδU : δ ≤ dU := (min_le_right _ _).trans (min_le_left _ _)
  have hδR : δ ≤ dR := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδC : δ ≤ dC := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hSub0 := commonRoom_mono y0 ρ hδ0le
  have hSubU := commonRoom_mono y0 ρ hδU
  have hSubR := commonRoom_mono y0 ρ hδR
  have hSubC := commonRoom_mono y0 ρ hδC
  have hPSubU : ParamRoom δ ⊆ ParamRoom dU := fun t ht => ⟨hSubU ht.1,ht.2⟩
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := hSubR.trans hRoomR
  have hSeg (t : Tpar) (ht : t ∈ ParamRoom δ) :=
    segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
  have hBaseSm (V : Generator) (j : Fin 3) := generator_E_both_smooth
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ hSub0 hRoom
    (fun V c => ⟨((hUS V c).1).mono hPSubU,((hUS V c).2).mono hPSubU⟩)
    (fun V => ⟨((hRS V).1).mono hSubR,((hRS V).2).mono hSubR⟩) V j
  have hLeftSm (V : Generator) (j : Fin 3) : ContDiffOn ℝ ∞ (CH hreg δ0 W V j) (ParamRoom δ) := by
    cases V with
    | inl ij => exact (hBaseSm (Sum.inl ij) j).1.neg
    | inr z => exact (hBaseSm (Sum.inr z) j).1
  have hRightSm (V : Generator) (j : Fin 3) : ContDiffOn ℝ ∞ (DH hreg δ0 W V j) (ParamRoom δ) :=
    (hBaseSm V j).2.neg
  have hDG (V : Generator) (j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u : Hi) :
      JL (DGE hreg δ0 W V j t u)=generatorLow V (eH j t u)-eL j t (generatorHigh V u) :=
    generatorReverseEHigh_graph_at g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W V j t ⟨hSub0 ht.1,ht.2⟩
      (fun z => (hRG V t.1 (hSubR ht.1) z).2)
      (fun c => (hUG V c t (hPSubU ht)).2) u
  have hGraphs (V : Generator) (j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u : Hi) :=
    pairedHigh_graphs_at g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W V j t
      (hCG V j t ⟨hSubC ht.1,ht.2⟩) (hDG V j t ht) u
  have hAdj (V : Generator) (j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u v : Hi) :
      PP (IH v) (JL (CH hreg δ0 W V j t u))=PP (IH u) (JL (DH hreg δ0 W V j t v)) :=
    actual_generator_E_paired_adjunction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W V j t ⟨hSub0 ht.1,ht.2⟩ (hSeg t ht)
      (fun z => (hGraphs V j t ht z).1) (fun z => (hGraphs V j t ht z).2) u v
  have hK := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  have hU : UniqueDiffOn ℝ (ParamRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _) ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  have hLow (V : Generator) (j : Fin 3) : ∃ Cl : Tpar → Half →L[ℝ] Neg,
      ContDiffOn ℝ ∞ Cl (ParamRoom δ) ∧ ∀ t ∈ ParamRoom δ,
        (Cl t).comp IH=(JL).comp (CH hreg δ0 W V j t) ∧
        (I33).comp (Cl t)=(v016TransposeL (DH hreg δ0 W V j t)).comp JL ∧
        ‖Cl t‖ ≤ (‖v016TransposeL (DH hreg δ0 W V j t)‖+‖CH hreg δ0 W V j t‖)/2 ∧
        ‖Cl t‖ ≤ (‖DH hreg δ0 W V j t‖+‖CH hreg δ0 W V j t‖)/2 :=
    v016_exists_contDiffOn_lowEndpoint (ParamRoom δ) hU (CH hreg δ0 W V j) (DH hreg δ0 W V j)
      (hLeftSm V j) (hRightSm V j) (hAdj V j)
  choose Cl hCl using hLow
  refine ⟨δ,hδ,hδ0le,hδU.trans hdUρ,hRoom,⟨{
    low := Cl, smoothLeft := hLeftSm, smoothRight := hRightSm, smoothLow := fun V j => (hCl V j).1,
    highGraph := fun V j t ht u => (hGraphs V j t ht u).1,
    partnerGraph := fun V j t ht u => (hGraphs V j t ht u).2,
    adjunction := hAdj,
    upper := fun V j t ht => ((hCl V j).2 t ht).1,
    lower := fun V j t ht => ((hCl V j).2 t ht).2.1,
    midpoint := fun V j t ht => ((hCl V j).2 t ht).2.2.2,
    finiteCaps := ?_ }⟩⟩
  intro N
  choose ML hML using fun z : Generator × Fin 3 => exists_compact_iteratedFDerivWithin_bound
    (CH hreg δ0 W z.1 z.2) (ParamRoom δ) hK hU (hLeftSm z.1 z.2) N
  choose MR hMR using fun z : Generator × Fin 3 => exists_compact_iteratedFDerivWithin_bound
    (DH hreg δ0 W z.1 z.2) (ParamRoom δ) hK hU (hRightSm z.1 z.2) N
  choose MC hMC using fun z : Generator × Fin 3 => exists_compact_iteratedFDerivWithin_bound
    (Cl z.1 z.2) (ParamRoom δ) hK hU (hCl z.1 z.2).1 N
  let M := ∑ z : Generator × Fin 3, (ML z+MR z+MC z)
  have h0 (z : Generator × Fin 3) : 0 ≤ ML z+MR z+MC z := by linarith [(hML z).1,(hMR z).1,(hMC z).1]
  refine ⟨M,Finset.sum_nonneg (fun z _ => h0 z),?_⟩
  intro V j n hn t ht
  have hOne : ML (V,j)+MR (V,j)+MC (V,j) ≤ M := Finset.single_le_sum (fun z _ => h0 z) (Finset.mem_univ (V,j))
  have a0 := (hML (V,j)).1
  have b0 := (hMR (V,j)).1
  have c0 := (hMC (V,j)).1
  exact ⟨((hML (V,j)).2 n hn t ht).trans (by linarith),
    ((hMR (V,j)).2 n hn t ht).trans (by linarith),((hMC (V,j)).2 n hn t ht).trans (by linarith)⟩

/-- No external analytic data: choose the ordinary actual W ONCE, then construct
all actual generator/E paired endpoints on that same retained witness set. -/
theorem exists_actual_generator_paired_packet
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ ρ ∧ ∃ W : CoeffRoom δ0,
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧ Nonempty (GenRoom hreg δ0 W δ) := by
  obtain ⟨δ0,hδ0,hδ0ρ,_hRoom,W,_hOrdS,_hOrdC,_hOrdP,_hZeroS,_hZeroG,_hOrdCaps⟩ :=
    exists_commonRoom_actual_fullE_ordinary_endpoints g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨δ,hδ,hδ0le,hδρ,hRoom,hP⟩ := exists_retained_generator_paired_endpoints
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  exact ⟨δ0,hδ0,hδ0ρ,W,δ,hδ,hδ0le,hδρ,hRoom,hP⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEPairedGainedEndpoints
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEPairedGainedEndpoints.exists_actual_generator_paired_packet
