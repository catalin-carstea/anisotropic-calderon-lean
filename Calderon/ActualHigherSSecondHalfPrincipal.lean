import Calderon.ActualConnectionGramCancellation
/- Root; exact source expansion precedes this file in UPFRONT.md. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSSecondHalfPrincipal
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

local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "OH" => ActualConnectionGramCancellation.connectionHigh g L
local notation "OL" => ActualConnectionGramCancellation.connectionLow g L
local notation "COH" => ActualConnectionGramCancellation.connectionCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
local notation "BL" => (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)

private lemma commutator_reassemble {M : Type*} [AddCommGroup M] (a b c : M)
    (h : c=a-b) : a=b+c := by rw [h]; abel
private lemma connection_reassemble {M : Type*} [AddCommGroup M] (a b c : M)
    (h : c=-b+a) : b=a-c := by rw [h]; abel

attribute [local irreducible] canonicalHigh canonicalLow pairedLeftHigh sphereSobolevInclusionL
  generatorHigh generatorLow ActualConnectionGramCancellation.connectionHigh
  ActualConnectionGramCancellation.connectionLow ActualConnectionGramCancellation.connectionCommutatorHigh

/-- Algebraic degree transport on a GENUINE first-word Hi lift. No inverse norm is used. -/
theorem degree_on_first_word (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δC : ℝ) (Cm : CRoom hreg δ0 W δC) (j : Fin 3) (t : Tpar)
    (htP : t ∈ ParamRoom δP) (htC : t ∈ ParamRoom δC) (u ub z : Hi)
    (hz : IH z=EH j t u) (hb : IH ub=BH u) :
    BH z=EH j t ub+CH hreg δ0 W BG j t u := by
  have hBCompat : JL (BH z)=BL (IH z) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A z) sphereSobolevShiftedDegree_high_half_compatibility
  have hE := (Cm.compat j t htC ub).trans (congrArg (EL j t) hb)
  have hGain : JL (CH hreg δ0 W BG j t u)=BL (EH j t u)-EL j t (BH u) := by
    simpa only [generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using P.highGraph BG j t htP u
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  calc
    _ = BL (EH j t u) := hBCompat.trans (congrArg (BL) hz)
    _ = EL j t (BH u)+JL (CH hreg δ0 W BG j t u) := commutator_reassemble _ _ _ hGain
    _ = JL (EH j t ub)+JL (CH hreg δ0 W BG j t u) :=
      congrArg (fun a => a+JL (CH hreg δ0 W BG j t u)) hE.symm
    _ = _ := (map_add (JL) _ _).symm

/-- Algebraic connection transport on the actual first-word lift, with its sharp sign. -/
theorem connection_on_first_word (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δC : ℝ) (Cm : CRoom hreg δ0 W δC) (m j : Fin 3) (t : Tpar)
    (htP : t ∈ ParamRoom δP) (htC : t ∈ ParamRoom δC) (u uOm z : Hi)
    (hz : IH z=EH j t u) (hOm : IH uOm=OH m t u) :
    OH m t z=EH j t uOm-COH hreg δ0 W m j t u := by
  have hOmCompat : JL (OH m t z)=OL m t (IH z) := by
    simpa only [ActualConnectionGramCancellation.connectionHigh,ActualConnectionGramCancellation.connectionLow,
      ContinuousLinearMap.comp_apply] using congrArg (fun A : Hi →L[ℝ] Neg => A z)
        (referenceHorizontalAngularL_high_lower_compatibility g L t.1.1 t.1.2.1 m)
  have hE := (Cm.compat j t htC uOm).trans (congrArg (EL j t) hOm)
  have hGain := ActualConnectionGramCancellation.connection_commutator_high_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P m j t htP u
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  calc
    _ = OL m t (EH j t u) := hOmCompat.trans (congrArg (OL m t) hz)
    _ = EL j t (OH m t u)-JL (COH hreg δ0 W m j t u) := connection_reassemble _ _ _ hGain
    _ = JL (EH j t uOm)-JL (COH hreg δ0 W m j t u) :=
      congrArg (fun a => a-JL (COH hreg δ0 W m j t u)) hE.symm
    _ = _ := (map_sub (JL) _ _).symm

section GenericDerivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Differentiate a GLOBAL genuine lift identity before applying the operator product rule. -/
theorem fderiv_global_lift_apply (I : E →L[ℝ] F) (V U : R3 → E) (A : R3 → E →L[ℝ] F)
    (x X : R3) (hV : DifferentiableAt ℝ V x) (hU : DifferentiableAt ℝ U x)
    (hA : DifferentiableAt ℝ A x) (hValue : ∀ y, I (V y)=A y (U y)) :
    I (fderiv ℝ V x X)=A x (fderiv ℝ U x X)+fderiv ℝ A x X (U x) := by
  have hLeft := congrArg (fun D : R3 →L[ℝ] F => D X) (I.hasFDerivAt.comp x hV.hasFDerivAt).fderiv
  have hFields : (fun y => I (V y))=(fun y => A y (U y)) := funext hValue
  have hFD := congrArg (fun f : R3 → F => fderiv ℝ f x X) hFields
  exact hLeft.symm.trans (hFD.trans
    (ActualHigherSCoefficientExtraction.fderiv_family_apply_point A U x X hA hU))
end GenericDerivative


local notation "PH" => ActualHigherSCoefficientExtraction.profileHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UOm" => ActualConnectionGramCancellation.connectionInput hO hD g hg L
local notation "UB" => ActualHigherSFormation.higherSDegreeInput hO hD
local notation "UD" => ActualHigherSFormation.higherSReferenceInput hO hD g L hg

attribute [local irreducible] ActualHigherSFormation.higherSInput
  ActualHigherSFormation.higherSDegreeInput ActualHigherSFormation.higherSReferenceInput
  ActualHigherSFormation.higherSLift referenceHighWeightedHorizontalAction

/-- The literal correction on the ORIGINAL second S word, as a Hi-to-Half operator. -/
def secondHalfCorrection (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δr Ar : ℝ) (p : ℕ) (q : ℝ) (i j : Fin 3) (x : R3) : Hi →L[ℝ] Half :=
  fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i)
    -COH hreg δ0 W i j ((Tq δr Ar p q) x)
    +referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i •
       CH hreg δ0 W BG j ((Tq δr Ar p q) x)
    +referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i •
       EH j ((Tq δr Ar p q) x)
    -∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
       (referenceMetricGramFrame g L (q,x) i) k j • EH k ((Tq δr Ar p q) x)

/-- Exact derivative of the original genuine first-word lift at a supported point. -/
theorem derivative_first_word (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δC : ℝ) (Cm : CRoom hreg δ0 W δC)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F, (Tq δr Ar p q) x ∈ ParamRoom δC)
    (j : Fin 3) (x X : R3) (hx : x ∈ TS F) :
    IH (fderiv ℝ (VF δr Ar p q hreg δ0 W F j) x X)=
      EH j ((Tq δr Ar p q) x) (fderiv ℝ (Uin F) x X)+
        fderiv ℝ (PH δr Ar p q j) x X (Uin F x) := by
  have hV := ActualCommonFirstWordQuadraticAdjoint.contDiff_fwdLift
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm
    δr Ar p hδr hAr q F hT j
  have hU : ContDiff ℝ ∞ (Uin F) := by
    simpa only [ActualHigherSFormation.higherSInput] using contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hA := ActualHigherSCoefficientExtraction.differentiableAt_profileHigh
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm
    δr Ar p hδr hAr q j x (hT x hx)
  exact fderiv_global_lift_apply IH (VF δr Ar p q hreg δ0 W F j) (Uin F)
    (PH δr Ar p q j) x X (hV.differentiable (by simp) x)
    (hU.differentiable (by simp) x) hA
    (ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm
      δr Ar p hδr hAr q F hT j)

private lemma weighted_action_reassembly {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : E →L[ℝ] G) (du uOm ub ud : E) (d c b : G) (f : ℝ)
    (hud : ud=du+uOm+f • ub) :
    (A du+d)+((A uOm-c)+f • (A ub+b))=A ud+(d-c+f • b) := by
  simp only [hud,map_add,map_smul,smul_add]
  abel

/-- ORIGINAL weighted derivative through VF, before adding connection/frame terms. -/
theorem weighted_action_first_word (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δC : ℝ) (Cm : CRoom hreg δ0 W δC)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F, (Tq δr Ar p q) x ∈ ParamRoom δC)
    (i j : Fin 3) (x : R3) (hx : x ∈ TS F)
    (htP : (Tq δr Ar p q) x ∈ ParamRoom δP) :
    referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
      (VF δr Ar p q hreg δ0 W F j) x i =
    EH j ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F i x)+
      (fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i) (Uin F x)
        -COH hreg δ0 W i j ((Tq δr Ar p q) x) (Uin F x)
        +referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i •
          CH hreg δ0 W BG j ((Tq δr Ar p q) x) (Uin F x)) := by
  let t := (Tq δr Ar p q) x
  let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i
  have hz := ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm
    δr Ar p hδr hAr q F hT j x
  have hb : IH (UB F x)=BH (Uin F x) := by
    simpa only [generatorHigh] using ActualDegreeGramCancellation.finite_degree_input_inclusion hO hD F x
  have hOm := ActualConnectionGramCancellation.connectionInput_inclusion
    g L hg hO hD δr Ar p hδr hAr q F i x
  have hB := degree_on_first_word g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δP P δC Cm j t htP (hT x hx) (Uin F x) (UB F x)
    (VF δr Ar p q hreg δ0 W F j x) hz hb
  have hOmega := connection_on_first_word g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δP P δC Cm i j t htP (hT x hx) (Uin F x)
    (UOm δr Ar p hδr hAr q F i x) (VF δr Ar p q hreg δ0 W F j x) hz hOm
  have hd := derivative_first_word g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δC Cm δr Ar p hδr hAr q F hT j x (referenceMetricGramFrame g L (q,x) i) hx
  have hud : UD δr Ar p hδr hAr q F i x=
      fderiv ℝ (Uin F) x (referenceMetricGramFrame g L (q,x) i)+
      UOm δr Ar p hδr hAr q F i x+f • UB F x := by
    dsimp only [ActualConnectionGramCancellation.connectionInput,f]
    abel
  have hOmegaActual : referenceHighHorizontalAngularL g L q x i (VF δr Ar p q hreg δ0 W F j x)=
      EH j t (UOm δr Ar p hδr hAr q F i x)-COH hreg δ0 W i j t (Uin F x) := by
    simpa only [t,ActualConnectionGramCancellation.connectionHigh,ActualHigherSFormation.higherSParam] using hOmega
  have hZero : ActualHigherSCoefficientExtraction.weightedHighZero
      g L q (referenceRadius δr Ar p L) x i (VF δr Ar p q hreg δ0 W F j x)=
      (EH j t (UOm δr Ar p hδr hAr q F i x)-COH hreg δ0 W i j t (Uin F x))+
        f • (EH j t (UB F x)+CH hreg δ0 W BG j t (Uin F x)) := by
    simp only [ActualHigherSCoefficientExtraction.weightedHighZero,add_apply,smul_apply]
    exact congrArg₂ (fun a b : Half => a+f • b) hOmegaActual hB
  calc
    _ = IH (fderiv ℝ (VF δr Ar p q hreg δ0 W F j) x (referenceMetricGramFrame g L (q,x) i))+
        ActualHigherSCoefficientExtraction.weightedHighZero g L q (referenceRadius δr Ar p L) x i
          (VF δr Ar p q hreg δ0 W F j x) :=
      ActualHigherSCoefficientExtraction.high_action_split g L q (referenceRadius δr Ar p L)
        (VF δr Ar p q hreg δ0 W F j) x i
    _ = (EH j t (fderiv ℝ (Uin F) x (referenceMetricGramFrame g L (q,x) i))+
          fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i) (Uin F x))+
        ((EH j t (UOm δr Ar p hδr hAr q F i x)-COH hreg δ0 W i j t (Uin F x))+
          f • (EH j t (UB F x)+CH hreg δ0 W BG j t (Uin F x))) :=
      congrArg₂ (fun a b : Half => a+b) hd hZero
    _ = _ := weighted_action_reassembly _ _ _ _ _ _ _ _ f hud


local notation "SC" => secondHalfCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Literal original second word: both principal orders and EVERY correction retained. -/
theorem original_second_word_half (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δC : ℝ) (Cm : CRoom hreg δ0 W δC)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F, (Tq δr Ar p q) x ∈ ParamRoom δC)
    (i j : Fin 3) (x : R3) (hx : x ∈ TS F)
    (htP : (Tq δr Ar p q) x ∈ ParamRoom δP) :
    ActualHigherSFormation.higherSSecondWordHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W F i j x =
      EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F j x)+
      EH j ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F i x)+
      SC hreg δ0 W δr Ar p q i j x (Uin F x) := by
  have hAct := weighted_action_first_word g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δP P δC Cm δr Ar p hδr hAr q F hT i j x hx htP
  have hz (k : Fin 3) := ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm
    δr Ar p hδr hAr q F hT k x
  have hSum : (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j • IH (VF δr Ar p q hreg δ0 W F k x))=
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j • EH k ((Tq δr Ar p q) x) (Uin F x) := by
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun z : Half => referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j • z) (hz k)
  let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i
  let oldSum := ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j • IH (VF δr Ar p q hreg δ0 W F k x)
  let newSum := ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j • EH k ((Tq δr Ar p q) x) (Uin F x)
  have hRest : f • IH (VF δr Ar p q hreg δ0 W F j x)-oldSum=
      f • EH j ((Tq δr Ar p q) x) (Uin F x)-newSum :=
    congrArg₂ (fun v s : Half => f • v-s) (hz j) hSum
  calc
    _ = referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
          (VF δr Ar p q hreg δ0 W F j) x i+
        EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F j x)+
        (f • IH (VF δr Ar p q hreg δ0 W F j x)-oldSum) := by
      unfold ActualHigherSFormation.higherSSecondWordHalf
      dsimp only [f,oldSum]
      abel
    _ = (EH j ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F i x)+
          (fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i) (Uin F x)
            -COH hreg δ0 W i j ((Tq δr Ar p q) x) (Uin F x)
            +f • CH hreg δ0 W BG j ((Tq δr Ar p q) x) (Uin F x)))+
        EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F j x)+
        (f • EH j ((Tq δr Ar p q) x) (Uin F x)-newSum) :=
      congrArg₂ (fun a b : Half => a+EH i ((Tq δr Ar p q) x)
        (UD δr Ar p hδr hAr q F j x)+b) hAct hRest
    _ = _ := by
      simp only [secondHalfCorrection,add_apply,sub_apply,smul_apply,sum_apply]
      dsimp only [f,newSum]
      abel

/-- The exact principal part of the ORIGINAL second-S Half field. -/
def secondHalfPrincipal (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  (referenceRadius δr Ar p L x)^2 • ∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
      (EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F j x)+
       EH j ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F i x))

/-- The full correction including the original normalized drift term. -/
def secondHalfError (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  (referenceRadius δr Ar p L x)^2 • ∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j • SC hreg δ0 W δr Ar p q i j x (Uin F x)+
  (referenceRadius δr Ar p L x)^2 • ∑ i : Fin 3,
    normalizedSecondDriftFrameJoint g g2 L i (q,x) • EH i ((Tq δr Ar p q) x) (Uin F x)

/-- Exact source identity, with no symmetry assumption on Q and no dropped drift. -/
theorem original_second_half (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δC : ℝ) (Cm : CRoom hreg δ0 W δC) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F, (Tq δr Ar p q) x ∈ ParamRoom δC)
    (x : R3) (hx : x ∈ TS F) (htP : (Tq δr Ar p q) x ∈ ParamRoom δP) :
    ActualHigherSFormation.higherSSecondHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F x =
    secondHalfPrincipal g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F x+
    secondHalfError g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p q F x := by
  have hWords (i j : Fin 3) := original_second_word_half
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δP P δC Cm δr Ar p hδr hAr q F hT i j x hx htP
  have hLift (i : Fin 3) := ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm
    δr Ar p hδr hAr q F hT i x
  simp only [ActualHigherSFormation.higherSSecondHalf,hWords,hLift,
    secondHalfPrincipal,secondHalfError,smul_add,Finset.sum_add_distrib]
  abel

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSSecondHalfPrincipal
