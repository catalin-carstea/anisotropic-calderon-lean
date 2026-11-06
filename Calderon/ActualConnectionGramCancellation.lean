import Calderon.ActualQDegreeBaseContraction
/- Root; exact mathematics in UPFRONT.md before code. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualConnectionGramCancellation
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
local notation "GRAM" => ActualDegreeGramCancellation.degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
/-- Literal original high connection, with point projections isolated from notation. -/
def connectionHigh (m : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  referenceHighHorizontalAngularL g L t.1.1 t.1.2.1 m
/-- Literal original low connection. -/
def connectionLow (m : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  referenceLowerHorizontalAngularL g L t.1.1 t.1.2.1 m
local notation "OmH" => connectionHigh g L
local notation "OmL" => connectionLow g L

/-- The literal original Gamma coefficient, independent of profile and input. -/
def connectionCoefficient (m a b : Fin 3) (t : Tpar) : ℝ :=
  referenceFrameConnectionCoefficient g L t.1.1 t.1.2.1
    (referenceMetricGramFrame g L (t.1.1,t.1.2.1) m) a b
local notation "GAM" => connectionCoefficient g L

/-- Actual sharp-connection commutator, from the ORIGINAL native rotation/E packet. -/
def connectionCommutatorHigh (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (m i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    GAM m a b t • CH hreg δ0 W (Sum.inl (a,b)) i t

/-- The genuine balanced low connection commutator on the SAME packet. -/
def connectionCommutatorLow {hreg : FixedDirichletRegularity} {δ0 : ℝ} {W : CoeffRoom δ0} {δP : ℝ}
    (P : GenRoom hreg δ0 W δP) (m i : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, GAM m a b t • P.low (Sum.inl (a,b)) i t
local notation "C_H" => connectionCommutatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "C_L" => connectionCommutatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

section GenericRows
variable {E1 E2 E3 : Type*}
  [NormedAddCommGroup E1] [NormedSpace ℝ E1]
  [NormedAddCommGroup E2] [NormedSpace ℝ E2]
  [NormedAddCommGroup E3] [NormedSpace ℝ E3]

private lemma weighted_rotation_graph (J : E2 →L[ℝ] E3) (B : E2 →L[ℝ] E3)
    (RH C : Fin 3 → Fin 3 → E1 →L[ℝ] E2) (RL : Fin 3 → Fin 3 → E2 →L[ℝ] E3)
    (c : Fin 3 → Fin 3 → ℝ) (u : E1) (v : E2)
    (hC : ∀ a b, J (C a b u)=-(RL a b v)+B (RH a b u)) :
    J (((1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • C a b) u)=
      -(((1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • RL a b) v)+
      B (((1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • RH a b) u) := by
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum,hC,
    smul_add,smul_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib]

private lemma weighted_low_graph (I : E1 →L[ℝ] E2) (J : E2 →L[ℝ] E3)
    (H : Fin 3 → Fin 3 → E1 →L[ℝ] E2) (L : Fin 3 → Fin 3 → E2 →L[ℝ] E3)
    (c : Fin 3 → Fin 3 → ℝ) (u : E1) (h : ∀ a b, L a b (I u)=J (H a b u)) :
    (((1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • L a b) (I u))=
      J (((1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • H a b) u) := by
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum,h]

private lemma connection_graph_rearrange {M : Type*} [AddCommGroup M]
    (a b c : M) (h : c=-b+a) : a=b+c := by rw [h]; abel
end GenericRows

attribute [local irreducible] canonicalHigh canonicalLow reverseELow pairedLeftHigh
  generatorHigh generatorLow sphereSobolevRotationL sphereSobolevInclusionL
  referenceMetricGramFrame referenceFrameConnectionCoefficient

/-- The exact high original connection commutator graph, including its sharp sign. -/
theorem connection_commutator_high_graph (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (m i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δP) (u : Hi) :
    JL (C_H hreg δ0 W m i t u)=-(OmL m t (EH i t u))+EL i t (OmH m t u) := by
  have hRot (a b : Fin 3) : JL (CH hreg δ0 W (Sum.inl (a,b)) i t u)=
      -(sphereSobolevRotationL (1/2 : ℝ) a b (EH i t u))+
        EL i t (sphereSobolevRotationL (3/2 : ℝ) a b u) := by
    simpa only [generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow,
      ContinuousLinearMap.neg_apply,map_neg,sub_neg_eq_add] using
      P.highGraph (Sum.inl (a,b)) i t ht u
  have hSum := weighted_rotation_graph (JL) (EL i t)
    (sphereSobolevRotationL (3/2 : ℝ)) (fun a b => CH hreg δ0 W (Sum.inl (a,b)) i t)
    (sphereSobolevRotationL (1/2 : ℝ)) (fun a b => GAM m a b t) u (EH i t u) hRot
  simpa only [connectionCommutatorHigh,connectionCoefficient,connectionHigh,connectionLow,referenceHighHorizontalAngularL,
    referenceLowerHorizontalAngularL] using hSum

/-- Exact upper compatibility of the genuine low connection commutator. -/
theorem connection_commutator_low_graph (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (m i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δP) (u : Hi) :
    C_L P m i t (IH u)=JL (C_H hreg δ0 W m i t u) := by
  have hUpper (a b : Fin 3) : P.low (Sum.inl (a,b)) i t (IH u)=
      JL (CH hreg δ0 W (Sum.inl (a,b)) i t u) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A u) (P.upper (Sum.inl (a,b)) i t ht)
  exact weighted_low_graph IH JL
    (fun a b => CH hreg δ0 W (Sum.inl (a,b)) i t)
    (fun a b => P.low (Sum.inl (a,b)) i t) (fun a b => GAM m a b t) u hUpper

/-- An original connection Hi lift feeds the canonical E graph without lifting any E output. -/
theorem connection_lift_E_graph (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δC : ℝ) (Cm : CRoom hreg δ0 W δC) (m i : Fin 3) (t : Tpar)
    (htP : t ∈ ParamRoom δP) (htC : t ∈ ParamRoom δC) (u uOm : Hi)
    (hOm : IH uOm=OmH m t u) :
    JL (EH i t uOm)=OmL m t (EH i t u)+JL (C_H hreg δ0 W m i t u) := by
  have hc := Cm.compat i t htC uOm
  have hComm := connection_commutator_high_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P m i t htP u
  exact hc.trans ((congrArg (EL i t) hOm).trans (connection_graph_rearrange _ _ _ hComm))

attribute [local irreducible] connectionCommutatorHigh connectionCommutatorLow
  connectionHigh connectionLow ActualDegreeGramCancellation.degreeGram

/-- Exact ORIGINAL connection Gram cancellation, using universal output skewness. -/
theorem connection_gram_cancellation (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δC : ℝ) (Cm : CRoom hreg δ0 W δC) (m i j : Fin 3) (t : Tpar)
    (htP : t ∈ ParamRoom δP) (htC : t ∈ ParamRoom δC) (u v uOm vOm : Hi)
    (hu : IH uOm=OmH m t u) (hv : IH vOm=OmH m t v) :
    GRAM i j t u vOm+GRAM i j t uOm v =
      PP (IH v) (eL j t (C_H hreg δ0 W m i t u))+
        PP (EH i t u) (C_L P m j t (IH v)) := by
  have hgi := connection_lift_E_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P δC Cm m i t htP htC u uOm hu
  have hgj := connection_lift_E_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P δC Cm m j t htP htC v vOm hv
  have hc := Cm.compat j t htC v
  have hUpper := connection_commutator_low_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P m j t htP v
  have hPair := ActualDegreeGramCancellation.low_reverse_pairing
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W δC
      (commonRoom_mono y0 ρ Cm.rev.le0) Cm.rev.room j t htC (C_H hreg δ0 W m i t u) (IH v)
  have hSym := v016_pairing_inclusion_symm (EH j t v) (C_H hreg δ0 W m i t u)
  have hMove : PP (EH j t v) (JL (C_H hreg δ0 W m i t u))=
      PP (IH v) (eL j t (C_H hreg δ0 W m i t u)) :=
    hSym.trans ((congrArg (PP (C_H hreg δ0 W m i t u)) hc).trans hPair)
  have hSkew : PP (EH i t u) (OmL m t (EH j t v))=-PP (EH j t v) (OmL m t (EH i t u)) := by
    simpa only [connectionLow] using halfPairing_lowerAngular_skew g L t.1.1 t.1.2.1 m (EH i t u) (EH j t v)
  have hAdd (x : Half) (a b : Neg) : PP x (a+b)=PP x a+PP x b := halfPairing_add_right x a b
  have hn1 := (congrArg (PP (EH i t u)) hgj).trans (hAdd _ _ _)
  have hn2 := (congrArg (PP (EH j t v)) hgi).trans (hAdd _ _ _)
  have hn3 := congrArg (PP (EH i t u)) hUpper
  have hp1 := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD (EH i t u) (EH j t vOm)
  have hp2 := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD (EH j t v) (EH i t uOm)
  have hp2' : PP (EH j t v) (JL (EH i t uOm))=⟪KL (EH i t uOm),KL (EH j t v)⟫_ℝ :=
    hp2.trans (real_inner_comm _ _)
  unfold ActualDegreeGramCancellation.degreeGram
  calc
    _ = PP (EH i t u) (JL (EH j t vOm))+PP (EH j t v) (JL (EH i t uOm)) :=
      congrArg₂ (fun a b : ℝ => a+b) hp1.symm hp2'.symm
    _ = _ := by linarith only [hn1,hn2,hn3,hMove,hSkew]

private lemma sum_pairing_bound (A : Half →L[ℝ] Neg) (C E : Hi →L[ℝ] Half)
    (D : Half →L[ℝ] Neg) (u : Hi) (v : Half) :
    |PP v (A (C u))+PP (E u) (D v)| ≤ (‖A‖*‖C‖+‖E‖*‖D‖)*‖u‖*‖v‖ := by
  have h1 : |PP v (A (C u))| ≤ ‖v‖*(‖A‖*(‖C‖*‖u‖)) := by
    calc
      _ ≤ ‖v‖*‖A (C u)‖ := abs_sphereSobolevDualPairing_le (1/2 : ℝ) v (A (C u))
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((A.le_opNorm (C u)).trans (mul_le_mul_of_nonneg_left (C.le_opNorm u) (norm_nonneg A))) (norm_nonneg v)
  have h2 : |PP (E u) (D v)| ≤ (‖E‖*‖u‖)*(‖D‖*‖v‖) :=
    (abs_sphereSobolevDualPairing_le (1/2 : ℝ) (E u) (D v)).trans
      (mul_le_mul (E.le_opNorm u) (D.le_opNorm v) (norm_nonneg _) (mul_nonneg (norm_nonneg E) (norm_nonneg u)))
  calc
    _ ≤ |PP v (A (C u))|+|PP (E u) (D v)| := abs_add_le _ _
    _ ≤ ‖v‖*(‖A‖*(‖C‖*‖u‖))+(‖E‖*‖u‖)*(‖D‖*‖v‖) := add_le_add h1 h2
    _ = _ := by ring

/-- Sharp mixed Hi/Half connection Gram bound after cancellation. -/
theorem connection_gram_cancellation_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δC : ℝ) (Cm : CRoom hreg δ0 W δC) (m i j : Fin 3) (t : Tpar)
    (htP : t ∈ ParamRoom δP) (htC : t ∈ ParamRoom δC) (u v uOm vOm : Hi)
    (hu : IH uOm=OmH m t u) (hv : IH vOm=OmH m t v) :
    |GRAM i j t u vOm+GRAM i j t uOm v| ≤
      (‖eL j t‖*‖C_H hreg δ0 W m i t‖+‖EH i t‖*‖C_L P m j t‖)*‖u‖*‖IH v‖ :=
  (congrArg abs (connection_gram_cancellation
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P δC Cm
      m i j t htP htC u v uOm vOm hu hv)).le.trans
    (sum_pairing_bound (eL j t) (C_H hreg δ0 W m i t) (EH i t) (C_L P m j t) u (IH v))

private lemma norm_connection_sum_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : Fin 3 → Fin 3 → ℝ) (A : Fin 3 → Fin 3 → E →L[ℝ] F) (MC MA : ℝ)
    (hMC : 0 ≤ MC) (hc : ∀ a b, |c a b| ≤ MC) (hA : ∀ a b, ‖A a b‖ ≤ MA) :
    ‖(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • A a b‖ ≤ 9*MC*MA := by
  have hSum : ‖∑ a : Fin 3, ∑ b : Fin 3, c a b • A a b‖ ≤ 9*MC*MA := by
    calc
      _ ≤ ∑ a : Fin 3, ‖∑ b : Fin 3, c a b • A a b‖ := norm_sum_le _ _
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖c a b • A a b‖ := Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
      _ ≤ ∑ _a : Fin 3, ∑ _b : Fin 3, MC*MA := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b _
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hc a b) (hA a b) (norm_nonneg _) hMC
      _ = _ := by simp; ring
  calc
    _ = ‖(1/2 : ℝ)‖*‖∑ a : Fin 3, ∑ b : Fin 3, c a b • A a b‖ := norm_smul _ _
    _ ≤ 1*(9*MC*MA) := mul_le_mul (by norm_num) hSum (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Actual connection high/low caps from the original finite Gamma sum and native packet. -/
theorem exists_connection_commutator_uniform_caps (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP) (δC : ℝ) :
    ∃ CO : ℝ, 0 ≤ CO ∧ ∀ m i : Fin 3, ∀ t : Tpar,
      t ∈ ParamRoom δP → t ∈ ParamRoom δC →
      ‖C_H hreg δ0 W m i t‖ ≤ CO ∧ ‖C_L P m i t‖ ≤ CO := by
  have hGeoFull := ActualHorizontalNormBridge.exists_reference_geometry_uniform_bounds g hg L
    (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  rcases hGeoFull with ⟨MG,hMG,hGeo⟩
  have hMG0 : 0 ≤ MG := le_trans zero_le_one hMG
  have hCapsFull := P.finiteCaps 0
  rcases hCapsFull with ⟨CG,hCG,hCaps⟩
  refine ⟨9*MG*CG,mul_nonneg (mul_nonneg (by norm_num) hMG0) hCG,?_⟩
  intro m i t htP htC
  have hGamma (a b : Fin 3) : |GAM m a b t| ≤ MG :=
    (hGeo t.1.1 htC.1.1 t.1.2.1 htC.1.2.1).2.2.2 m a b
  have hCH (a b : Fin 3) : ‖CH hreg δ0 W (Sum.inl (a,b)) i t‖ ≤ CG := by
    have h := (hCaps (Sum.inl (a,b)) i 0 (le_refl 0) t htP).1
    simpa only [norm_iteratedFDerivWithin_zero] using h
  have hCL (a b : Fin 3) : ‖P.low (Sum.inl (a,b)) i t‖ ≤ CG := by
    have h := (hCaps (Sum.inl (a,b)) i 0 (le_refl 0) t htP).2.2
    simpa only [norm_iteratedFDerivWithin_zero] using h
  constructor
  · unfold connectionCommutatorHigh
    exact norm_connection_sum_le (E := Hi) (F := Half) (fun a b => GAM m a b t)
      (fun a b => CH hreg δ0 W (Sum.inl (a,b)) i t) MG CG hMG0 hGamma hCH
  · unfold connectionCommutatorLow
    exact norm_connection_sum_le (E := Half) (F := Neg) (fun a b => GAM m a b t)
      (fun a b => P.low (Sum.inl (a,b)) i t) MG CG hMG0 hGamma hCL

/-- One original connection Gram bound on the same two actual retained rooms. -/
theorem exists_actual_connection_gram_uniform_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δP : ℝ) (P : GenRoom hreg δ0 W δP)
    (δC : ℝ) (Cm : CRoom hreg δ0 W δC) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m i j : Fin 3, ∀ t : Tpar,
      t ∈ ParamRoom δP → t ∈ ParamRoom δC → ∀ u v uOm vOm : Hi,
      IH uOm=OmH m t u → IH vOm=OmH m t v →
      |GRAM i j t u vOm+GRAM i j t uOm v| ≤ K*‖u‖*‖IH v‖ := by
  have hCFull := exists_connection_commutator_uniform_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P δC
  rcases hCFull with ⟨CO,hCO,hCCap⟩
  have hEFull := ActualDegreeGramBaseDerivative.exists_actual_canonical_value_first_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm
  rcases hEFull with ⟨CE,hCE,hECap⟩
  have heFull := ActualHigherSAdjointCoefficientBounds.exists_retained_reverse_uniform_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm
  rcases heFull with ⟨_CH,Ce,_CH1,_hCH,hCe,_hCH1,_hEH,heCap,_hdEH⟩
  have hCe0 : 0 ≤ Ce := le_trans zero_le_one hCe
  refine ⟨Ce*CO+CE*CO,add_nonneg (mul_nonneg hCe0 hCO) (mul_nonneg hCE hCO),?_⟩
  intro m i j t htP htC u v uOm vOm hu hv
  have hRaw := connection_gram_cancellation_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P δC Cm
      m i j t htP htC u v uOm vOm hu hv
  have hBudget : ‖eL j t‖*‖C_H hreg δ0 W m i t‖+‖EH i t‖*‖C_L P m j t‖ ≤ Ce*CO+CE*CO :=
    add_le_add (mul_le_mul (heCap j t htC) (hCCap m i t htP htC).1
      (norm_nonneg (C_H hreg δ0 W m i t)) hCe0)
      (mul_le_mul (hECap i t htC).1 (hCCap m j t htP htC).2 (norm_nonneg (C_L P m j t)) hCE)
  exact hRaw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hBudget (norm_nonneg u)) (norm_nonneg (IH v)))

/-- ANY original caller W admits a common radius and uniform connection Gram cancellation. -/
theorem exists_retained_connection_gram_bound (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ m i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u v uOm vOm : Hi,
      IH uOm=OmH m t u → IH vOm=OmH m t v →
      |GRAM i j t u vOm+GRAM i j t uOm v| ≤ K*‖u‖*‖IH v‖ := by
  have hPFull := exists_retained_generator_paired_endpoints
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hPFull with ⟨δP,hδP,hδP0,hδPρ,_hRoomP,⟨P⟩⟩
  have hCmFull := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hCmFull with ⟨δC,Cm⟩
  have hFull := exists_actual_connection_gram_uniform_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δP P δC Cm
  rcases hFull with ⟨K,hK,hBound⟩
  let δ := min δP δC
  have hδPle : δ ≤ δP := min_le_left _ _
  have hδCle : δ ≤ δC := min_le_right _ _
  have hSP := commonRoom_mono y0 ρ hδPle
  have hSC := commonRoom_mono y0 ρ hδCle
  refine ⟨δ,lt_min hδP Cm.rev.pos,hδPle.trans hδP0,hδPle.trans hδPρ,K,hK,?_⟩
  intro m i j t ht u v uOm vOm hu hv
  exact hBound m i j t ⟨hSP ht.1,ht.2⟩ ⟨hSC ht.1,ht.2⟩ u v uOm vOm hu hv

/-- The ORIGINAL finite connection input, obtained by subtracting the original
base derivative and logarithmic-degree contribution from the original weighted input. -/
def connectionInput (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (m : Fin 3) (x : R3) : Hi :=
  ActualHigherSFormation.higherSReferenceInput hO hD g L hg δr Ar p hδr hAr q F m x-
    fderiv ℝ (ActualHigherSFormation.higherSInput hO hD F) x (referenceMetricGramFrame g L (q,x) m)-
    referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x m •
      ActualHigherSFormation.higherSDegreeInput hO hD F x
local notation "UOm" => connectionInput hO hD g hg L

private lemma connection_input_graph_from_split {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : E →L[ℝ] F) (ud du ub : E) (z b : F) (f : ℝ)
    (hD : I ud=I du+z+f • b) (hB : I ub=b) : I (ud-du-f • ub)=z := by
  simp only [map_sub,map_smul,hD,hB]
  abel

/-- The exact original connection input graph, global in x and without E-output finiteness. -/
theorem connectionInput_inclusion (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (m : Fin 3) (x : R3) :
    IH (UOm δr Ar p hδr hAr q F m x)=OmH m ((Tq δr Ar p q) x) (Uin F x) := by
  let R := referenceRadius δr Ar p L
  let f := referenceRadiusHorizontalLogDerivative g L q R x m
  let du := fderiv ℝ (Uin F) x (referenceMetricGramFrame g L (q,x) m)
  let ud := ActualHigherSFormation.higherSReferenceInput hO hD g L hg δr Ar p hδr hAr q F m x
  let ub := ActualHigherSFormation.higherSDegreeInput hO hD F x
  let b : Half := sphereSobolevShiftedDegreeL (3/2 : ℝ) (Uin F x)
  have hB : IH ub=b := by
    simpa only [ub,b,generatorHigh] using ActualDegreeGramCancellation.finite_degree_input_inclusion hO hD F x
  have hDInput := ActualHigherSSecondAdjoint.referenceInput_inclusion hO hD g hg L q δr Ar p hδr hAr F m x
  have hSplit := ActualHigherSCoefficientExtraction.high_action_split g L q R (Uin F) x m
  have hInput : IH ud=IH du+OmH m ((Tq δr Ar p q) x) (Uin F x)+f • b := by
    calc
      _ = referenceHighWeightedHorizontalAction g L q R (Uin F) x m := hDInput
      _ = IH du+ActualHigherSCoefficientExtraction.weightedHighZero g L q R x m (Uin F x) := hSplit
      _ = _ := by
        simp only [ActualHigherSCoefficientExtraction.weightedHighZero,add_apply,smul_apply,
          connectionHigh,ActualHigherSFormation.higherSParam]
        dsimp only [f,b]
        abel
  unfold connectionInput
  exact connection_input_graph_from_split IH ud du ub
    (OmH m ((Tq δr Ar p q) x) (Uin F x)) b f hInput hB

/-- Fully actual original finite inputs discharge the connection-lift hypotheses.
One W/radius and constant precede all profiles, finite inputs and angular sizes. -/
theorem exists_retained_finite_connection_gram_bound (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar, ∀ q : ℝ,
      ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ m i j : Fin 3, ∀ x : R3,
      (Tq δr Ar p q) x ∈ ParamRoom δ →
      |GRAM i j ((Tq δr Ar p q) x) (Uin F x) (UOm δr Ar p hδr hAr q G m x)+
        GRAM i j ((Tq δr Ar p q) x) (UOm δr Ar p hδr hAr q F m x) (Uin G x)| ≤
        K*‖Uin F x‖*‖IH (Uin G x)‖ := by
  have hFull := exists_retained_connection_gram_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hFull with ⟨δ,hδ,hδ0le,hδρ,K,hK,hBound⟩
  refine ⟨δ,hδ,hδ0le,hδρ,K,hK,?_⟩
  intro δr Ar p hδr hAr q F G m i j x ht
  exact hBound m i j ((Tq δr Ar p q) x) ht (Uin F x) (Uin G x)
    (UOm δr Ar p hδr hAr q F m x) (UOm δr Ar p hδr hAr q G m x)
    (connectionInput_inclusion g L hg hO hD δr Ar p hδr hAr q F m x)
    (connectionInput_inclusion g L hg hO hD δr Ar p hδr hAr q G m x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualConnectionGramCancellation
