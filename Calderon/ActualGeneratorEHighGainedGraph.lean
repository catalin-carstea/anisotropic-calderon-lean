import Calderon.ActualCanonicalGeneratorAngularGainedRows
import Calderon.ActualGeneratorRadialGainedRows
import Calderon.ActualWeightedHorizontalActions

/-! Source-only Sol author candidate. Exact upfront generator-E-high-before-v001.
Actual HIGH graph only; full W/E reverse partner/paired low/caps are deferred. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEHighGainedGraph
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

section Algebra
variable {E F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N]
private lemma orderOne_rightMultiplier_graph
    (I : E →L[ℝ] F) (J : F →L[ℝ] N) (VH TH : E →L[ℝ] F) (VL TL : F →L[ℝ] N)
    (PH : E →L[ℝ] E) (PL : F →L[ℝ] F) (D : E →L[ℝ] F) (U : E →L[ℝ] E)
    (hD : ∀ u, J (D u)=VL (TH u)-TL (VH u))
    (hT : ∀ u, J (TH u)=TL (I u))
    (hU : ∀ u, I (U u)=VH (PH u)-PL (VH u)) (u : E) :
    J ((D.comp PH+TH.comp U) u)=VL (TH (PH u))-TL (PL (VH u)) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add,hD,hT,hU,map_sub]
  abel
end Algebra

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
def generatorRaisingHigh (V : Generator) (m : Fin 3) : Hi →L[ℝ] Half :=
  match V with
  | Sum.inl ij => rotationRaisingHigh hF hO hD ij.1 ij.2 m
  | Sum.inr _ => raisingHigh hF hO hD m
private lemma generatorRaisingHigh_graph (V : Generator) (m : Fin 3) (u : Hi) :
    JL (generatorRaisingHigh hF hO hD V m u)=generatorLow V (raisingHigh hF hO hD m u)-
      raisingLow hF hO hD m (generatorHigh V u) := by
  cases V with
  | inl ij => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) (rotationRaisingHigh_graph hF hO hD ij.1 ij.2 m)
  | inr z => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) (degreeRaisingHigh_graph hF hO hD m)
private lemma generator_endpoint_compatibility (V : Generator) (u : Hi) :
    JL (generatorHigh V u)=generatorLow V (IH u) := by
  cases V with
  | inl ij => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) (sphereSobolevRotationL_threehalf_half_compatibility ij.1 ij.2)
  | inr z => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) sphereSobolevShiftedDegree_high_half_compatibility

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

/-- The complete actual [V,E_j] high gain, with H1 and H0 retained. -/
def generatorEHigh (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (V : Generator) (j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (generatorAdjointRadialHigh g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg V t.1).comp
      (NH (QW δ0 W (Sum.inl j) t)) + (Th t.1).comp (GH δ0 W V (Sum.inl j) t) +
  (∑ m : Fin 3, ((generatorRaisingHigh hF hO hD V m).comp (NH (QW δ0 W (Sum.inr (j,m)) t))+
    (raisingHigh hF hO hD m).comp (GH δ0 W V (Sum.inr (j,m)) t))) +
  (generatorHigh V).comp (ZH j t.1)-(ZL j t.1).comp (generatorHigh V)
local notation "CGE" => generatorEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  raisingHigh raisingLow generatorRaisingHigh generatorHigh generatorLow
  adjointHighRemainder adjointHalfRemainder generatorAdjointRadialHigh
  retainedGeneratorHigh generatorMultiplierHigh generatorMultiplierGains
  canonicalHigh canonicalLow generatorEHigh zeroCorrectionHigh zeroCorrectionHalf
  sphereSobolevInclusionL referencePiThreeHalfMultiplier referencePiHalfMultiplier

@[instance_reducible] private def geOriginalValueNormed : NormedAddCommGroup Hi := inferInstance
@[instance_reducible] private def geOriginalValueModule : NormedSpace ℝ Hi := inferInstance
@[instance_reducible] private def geOriginalMapNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def geOriginalMapModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def geValueNormed : NormedAddCommGroup Hi := geOriginalValueNormed
attribute [local instance] geValueNormed
@[instance_reducible] private def geValueModule : NormedSpace ℝ Hi := geOriginalValueModule
attribute [local instance] geValueModule
@[instance_reducible] private def geMapNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := geOriginalMapNormed
attribute [local instance] geMapNormed
@[instance_reducible] private def geMapModule : NormedSpace ℝ (Hi →L[ℝ] Half) := geOriginalMapModule
attribute [local instance] geMapModule
private theorem geValueNormed_canonical : geValueNormed = geOriginalValueNormed := rfl
private theorem geValueModule_canonical : geValueModule = geOriginalValueModule := rfl
private theorem geMapNormed_canonical : geMapNormed = geOriginalMapNormed := rfl
private theorem geMapModule_canonical : geMapModule = geOriginalMapModule := rfl

private theorem generatorEHigh_graph_at
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (V : Generator) (j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hRad : ∀ u : Hi, JL (generatorAdjointRadialHigh g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg V t.1 u)=
      generatorLow V (Th t.1 u)-Tl t.1 (generatorHigh V u))
    (hU : ∀ c : RetainedCoefficient, ∀ u : Hi, IH (GH δ0 W V c t u)=
      generatorHigh V (NH (QW δ0 W c t) u)-NL (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorHigh V u)) (u : Hi) :
    JL (CGE hreg δ0 W V j t u)=generatorLow V (EH j t u)-EL j t (generatorHigh V u) := by
  have hPi := (W.piGerm j t ht).self_of_nhds
  have hR0 := orderOne_rightMultiplier_graph IH JL (generatorHigh V) (Th t.1) (generatorLow V) (Tl t.1)
    (NH (QW δ0 W (Sum.inl j) t)) (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t)))
    (generatorAdjointRadialHigh g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg V t.1)
    (GH δ0 W V (Sum.inl j) t) hRad
    (fun z => v016_actual_Th_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg z)
    (hU (Sum.inl j)) u
  have hR : JL (((generatorAdjointRadialHigh g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg V t.1).comp
      (NH (QW δ0 W (Sum.inl j) t)) + (Th t.1).comp (GH δ0 W V (Sum.inl j) t)) u)=
      generatorLow V (Th t.1 (PiH j t u))-Tl t.1 (PiL j t (generatorHigh V u)) := by
    simpa only [retainedJets,piJets,hPi.1,hPi.2.1] using hR0
  have hA (m : Fin 3) :
      JL (((generatorRaisingHigh hF hO hD V m).comp (NH (QW δ0 W (Sum.inr (j,m)) t))+
        (raisingHigh hF hO hD m).comp (GH δ0 W V (Sum.inr (j,m)) t)) u)=
      generatorLow V (raisingHigh hF hO hD m (NH (NJ3 j m t.1) u))-
        raisingLow hF hO hD m (NL (NJ2 j m t.1) (generatorHigh V u)) := by
    have hNative := orderOne_rightMultiplier_graph IH JL (generatorHigh V)
      (raisingHigh hF hO hD m) (generatorLow V) (raisingLow hF hO hD m)
      (NH (QW δ0 W (Sum.inr (j,m)) t)) (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t)))
      (generatorRaisingHigh hF hO hD V m) (GH δ0 W V (Sum.inr (j,m)) t)
      (generatorRaisingHigh_graph hF hO hD V m) (v017_inclusion_raisingHigh hF hO hD m)
      (hU (Sum.inr (j,m))) u
    have hN := (W.jacobiGerm j m t.1 ht.1).self_of_nhds
    simpa only [retainedJets,jacobiJets,hN.1,hN.2.1] using hNative
  have hZero : JL ((generatorHigh V) (ZH j t.1 u))=
      generatorLow V (IH (ZH j t.1 u)) := generator_endpoint_compatibility V _
  have hSum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl (fun m _ => hA m)
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add] at hR hSum
  simp only [generatorEHigh,canonicalHigh,canonicalLow,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sub,map_sum,hZero]
  have hMain := congrArg₂ (fun x y : Neg =>
      (x+y+generatorLow V (IH (ZH j t.1 u))) - JL (ZL j t.1 (generatorHigh V u))) hR hSum
  exact hMain.trans (by
    simp only [Finset.sum_sub_distrib]
    abel)

/-- Actual full E high graph for ALL constant rotations and physical degree on
one room and the retained original Pi/Jacobi witness set. -/
private def actualGeneratorEHighFoldedContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ V : Generator, ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (CGE hreg δ0 W V j t u)=generatorLow V (EH j t u)-EL j t (generatorHigh V u)
attribute [local irreducible] actualGeneratorEHighFoldedContract
private theorem actualGeneratorEHighFoldedContract_proof
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    actualGeneratorEHighFoldedContract hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg δ0 W := by
  obtain ⟨dU,hdU,_hdU0,hdUρ,_hUS,hUG,_hUC⟩ :=
    exists_commonRoom_retained_generator_multiplier_gains g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel δ0 hδ0 W
  obtain ⟨dR,hdR,_hdRρ,hRoomR,_hRS,hRG,_hRC⟩ :=
    exists_commonRoom_actual_generator_radial_high_gains g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let δ := min δ0 (min dU dR)
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdU hdR)
  have hδU : δ ≤ dU := (min_le_right _ _).trans (min_le_left _ _)
  have hδR : δ ≤ dR := (min_le_right _ _).trans (min_le_right _ _)
  have hSub0 := commonRoom_mono y0 ρ (show δ ≤ δ0 from min_le_left _ _)
  have hSubU := commonRoom_mono y0 ρ hδU
  have hSubR := commonRoom_mono y0 ρ hδR
  unfold actualGeneratorEHighFoldedContract
  refine ⟨δ,hδ,min_le_left _ _,hδU.trans hdUρ,?_⟩
  intro V j t ht u
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoomR t.1 (hSubR ht.1)
  exact generatorEHigh_graph_at hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    hreg δ0 W V j t ⟨hSub0 ht.1,ht.2⟩ hSeg
    (fun z => (hRG V t.1 (hSubR ht.1) z).1)
    (fun c => (hUG V c t ⟨hSubU ht.1,ht.2⟩).1) u



theorem exists_commonRoom_actual_generator_E_high_graphs
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ V : Generator, ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (CGE hreg δ0 W V j t u)=generatorLow V (EH j t u)-EL j t (generatorHigh V u) := by
  simpa only [actualGeneratorEHighFoldedContract] using
    (actualGeneratorEHighFoldedContract_proof hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg hKernel δ0 hδ0 W)

/-- Literal angular reverse of the ACTUAL weighted horizontal angular map. -/
def weightedAngularReverseHigh (R : R3 → ℝ) (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  -referenceHighHorizontalAngularL g L t.1.1 t.1.2.1 i+
    referenceRadiusHorizontalLogDerivative g L t.1.1 R t.1.2.1 i • sphereSobolevShiftedDegreeL (3/2 : ℝ)
def weightedAngularReverseLow (R : R3 → ℝ) (i : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  -referenceLowerHorizontalAngularL g L t.1.1 t.1.2.1 i+
    referenceRadiusHorizontalLogDerivative g L t.1.1 R t.1.2.1 i • sphereSobolevShiftedDegreeL (1/2 : ℝ)

/-- Actual [W_i^sharp,E_j] high gain. The separate base derivative and explicit
f_i E_j dictionary term are not components of this angular map. -/
def weightedAngularEHigh (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (R : R3 → ℝ) (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  -((1/2 : ℝ) • ∑ aa : Fin 3, ∑ bb : Fin 3,
    referenceFrameConnectionCoefficient g L t.1.1 t.1.2.1 (referenceMetricGramFrame g L (t.1.1,t.1.2.1) i) aa bb •
      CGE hreg δ0 W (Sum.inl (aa,bb)) j t)+
    referenceRadiusHorizontalLogDerivative g L t.1.1 R t.1.2.1 i • CGE hreg δ0 W (Sum.inr ()) j t

/-- Literal actual weighted Wsharp/E HIGH graph; LOW/smooth/caps are deferred. -/
private def actualWeightedAngularEHighFoldedContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ (R : R3 → ℝ) (i j : Fin 3), ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (weightedAngularEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg δ0 W R i j t u)=
          weightedAngularReverseLow g L R i t (EH j t u)-
            EL j t (weightedAngularReverseHigh g L R i t u)
attribute [local irreducible] actualWeightedAngularEHighFoldedContract
private theorem actualWeightedAngularEHighFoldedContract_proof
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    actualWeightedAngularEHighFoldedContract hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg δ0 W := by
  obtain ⟨δ,hδ,hδ0le,hδρ,hG⟩ := exists_commonRoom_actual_generator_E_high_graphs
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg hKernel δ0 hδ0 W
  unfold actualWeightedAngularEHighFoldedContract
  refine ⟨δ,hδ,hδ0le,hδρ,?_⟩
  intro R i j t ht u
  have hAll (V : Generator) : JL (CGE hreg δ0 W V j t u)=
      generatorLow V (EH j t u)-EL j t (generatorHigh V u) := hG V j t ht u
  simp only [weightedAngularEHigh,weightedAngularReverseHigh,weightedAngularReverseLow,
    referenceHighHorizontalAngularL,referenceLowerHorizontalAngularL,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,map_add,map_neg,map_smul,map_sum,hAll,
    generatorHigh,generatorLow]
  simp only [smul_sub,Finset.smul_sum,Finset.sum_sub_distrib,neg_sub]
  abel


theorem exists_commonRoom_actual_weightedAngular_E_high_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ (R : R3 → ℝ) (i j : Fin 3), ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (weightedAngularEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg δ0 W R i j t u)=
          weightedAngularReverseLow g L R i t (EH j t u)-
            EL j t (weightedAngularReverseHigh g L R i t u) := by
  simpa only [actualWeightedAngularEHighFoldedContract] using
    (actualWeightedAngularEHighFoldedContract_proof hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg hKernel δ0 hδ0 W)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEHighGainedGraph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEHighGainedGraph.exists_commonRoom_actual_weightedAngular_E_high_graph
