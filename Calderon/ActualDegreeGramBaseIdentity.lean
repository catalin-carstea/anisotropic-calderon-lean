import Calderon.ActualDegreeGramBaseDerivative
/- Root; before-code expansion in UPFRONT.md. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualDegreeGramBaseIdentity
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
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

section GenericCalculus
variable {X0 P0 E0 F0 H0 : Type*}
  [NormedAddCommGroup X0] [NormedSpace ℝ X0]
  [NormedAddCommGroup P0] [NormedSpace ℝ P0]
  [NormedAddCommGroup E0] [NormedSpace ℝ E0]
  [NormedAddCommGroup F0] [NormedSpace ℝ F0]
  [NormedAddCommGroup H0] [InnerProductSpace ℝ H0]

/-- Differentiate the full physical Gram expression with its four original product terms. -/
theorem fderiv_physical_gram (K : F0 →L[ℝ] H0) (A B : P0 → E0 →L[ℝ] F0)
    (T : X0 → P0) (U V : X0 → E0) (x X : X0)
    (hA : DifferentiableAt ℝ A (T x)) (hB : DifferentiableAt ℝ B (T x))
    (hT : DifferentiableAt ℝ T x) (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) :
    fderiv ℝ (fun y => ⟪K (A (T y) (U y)),K (B (T y) (V y))⟫_ℝ) x X =
      ⟪K (fderiv ℝ A (T x) (fderiv ℝ T x X) (U x)),K (B (T x) (V x))⟫_ℝ+
      ⟪K (A (T x) (fderiv ℝ U x X)),K (B (T x) (V x))⟫_ℝ+
      ⟪K (A (T x) (U x)),K (fderiv ℝ B (T x) (fderiv ℝ T x X) (V x))⟫_ℝ+
      ⟪K (A (T x) (U x)),K (B (T x) (fderiv ℝ V x X))⟫_ℝ := by
  have hLeft := K.hasFDerivAt.comp x ((hA.hasFDerivAt.comp x hT.hasFDerivAt).clm_apply hU.hasFDerivAt)
  have hRight := K.hasFDerivAt.comp x ((hB.hasFDerivAt.comp x hT.hasFDerivAt).clm_apply hV.hasFDerivAt)
  have hInner := (hLeft.inner ℝ hRight).fderiv
  have hValue := congrArg (fun Q : X0 →L[ℝ] ℝ => Q X) hInner
  simp only [Function.comp_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,fderivInnerCLM_apply,
    add_apply,ContinuousLinearMap.flip_apply,map_add,inner_add_left,inner_add_right] at hValue
  linarith only [hValue]

/-- A global original input graph differentiates without any extra degree-lift hypothesis. -/
theorem fderiv_global_input_graph (I B : E0 →L[ℝ] F0) (U UB : X0 → E0) (x X : X0)
    (hU : DifferentiableAt ℝ U x) (hUB : DifferentiableAt ℝ UB x)
    (hGraph : ∀ y, I (UB y)=B (U y)) :
    I (fderiv ℝ UB x X)=B (fderiv ℝ U x X) := by
  have hLeft := (I.hasFDerivAt.comp x hUB.hasFDerivAt).fderiv
  have hRight := (B.hasFDerivAt.comp x hU.hasFDerivAt).fderiv
  have hFunctions : (fun y => I (UB y))=(fun y => B (U y)) := funext hGraph
  have hEq := congrArg (fun f : X0 → F0 => fderiv ℝ f x) hFunctions
  have hDeriv := hLeft.symm.trans (hEq.trans hRight)
  exact congrArg (fun Q : X0 →L[ℝ] F0 => Q X) hDeriv
end GenericCalculus

local notation "UBin" => ActualHigherSFormation.higherSDegreeInput hO hD
local notation "GRAM" => ActualDegreeGramCancellation.degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "COEF" => ActualDegreeGramBaseDerivative.degreeGramCoefficientDerivative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact differentiated original finite degree input graph. -/
theorem finite_degree_derivative_inclusion (F : smoothCompactFiniteSphereCore hO hD) (x X : R3) :
    IH (fderiv ℝ (UBin F) x X)=generatorHigh BG (fderiv ℝ (Uin F) x X) := by
  have hU : DifferentiableAt ℝ (Uin F) x :=
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F).differentiable (by simp) x
  have hUB : DifferentiableAt ℝ (UBin F) x :=
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F)).differentiable (by simp) x
  exact fderiv_global_input_graph IH (generatorHigh BG) (Uin F) (UBin F) x X hU hUB
    (fun y => ActualDegreeGramCancellation.finite_degree_input_inclusion hO hD F y)

/-- Literal scalar degree Gram field for the original finite input and original degree lift. -/
def finiteDegreeGramField (i j : Fin 3) (T : R3 → Tpar)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ := GRAM i j (T x) (Uin F x) (UBin F x)

/-- Full physical base derivative keeps both coefficient rows and both input derivatives. -/
theorem finite_degree_gram_fderiv (i j : Fin 3) (T : R3 → Tpar)
    (F : smoothCompactFiniteSphereCore hO hD) (x X : R3)
    (hi : DifferentiableAt ℝ (EH i) (T x)) (hj : DifferentiableAt ℝ (EH j) (T x))
    (hT : DifferentiableAt ℝ T x) :
    fderiv ℝ (finiteDegreeGramField g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j T F) x X =
      COEF i j (T x) (fderiv ℝ T x X) (Uin F x) (UBin F x)+
      GRAM i j (T x) (fderiv ℝ (Uin F) x X) (UBin F x)+
      GRAM i j (T x) (Uin F x) (fderiv ℝ (UBin F) x X) := by
  have hU : DifferentiableAt ℝ (Uin F) x :=
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F).differentiable (by simp) x
  have hUB : DifferentiableAt ℝ (UBin F) x :=
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F)).differentiable (by simp) x
  have hFull := fderiv_physical_gram (KL) (EH i) (EH j) T (Uin F) (UBin F) x X hi hj hT hU hUB
  unfold finiteDegreeGramField ActualDegreeGramCancellation.degreeGram
    ActualDegreeGramBaseDerivative.degreeGramCoefficientDerivative
  convert hFull using 1 <;> ring

/-- Original signed degree/base commutator row, with both ordered terms retained. -/
def finiteDegreeGramCommutator (i j : Fin 3) (T : R3 → Tpar)
    (F : smoothCompactFiniteSphereCore hO hD) (x X : R3) : ℝ :=
  GRAM i j (T x) (Uin F x) (fderiv ℝ (UBin F) x X)-
    GRAM i j (T x) (UBin F x) (fderiv ℝ (Uin F) x X)

local notation "FIELD" => finiteDegreeGramField g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "COMM" => finiteDegreeGramCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
attribute [local irreducible] ActualDegreeGramCancellation.degreeGram
  ActualDegreeGramBaseDerivative.degreeGramCoefficientDerivative finiteDegreeGramField
  finiteDegreeGramCommutator ActualHigherSFormation.higherSInput ActualHigherSFormation.higherSDegreeInput

/-- Exact symmetrized base/degree identity; no symmetry of Q or output truncation. -/
theorem finite_degree_gram_base_signed_identity (i j : Fin 3) (T : R3 → Tpar)
    (F : smoothCompactFiniteSphereCore hO hD) (x X : R3)
    (hi : DifferentiableAt ℝ (EH i) (T x)) (hj : DifferentiableAt ℝ (EH j) (T x))
    (hT : DifferentiableAt ℝ T x) :
    GRAM i j (T x) (fderiv ℝ (Uin F) x X) (UBin F x)+
      GRAM i j (T x) (UBin F x) (fderiv ℝ (Uin F) x X)-
      fderiv ℝ (FIELD i j T F) x X =
      -COEF i j (T x) (fderiv ℝ T x X) (Uin F x) (UBin F x)-COMM i j T F x X := by
  have hDerivative := finite_degree_gram_fderiv
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j T F x X hi hj hT
  unfold finiteDegreeGramCommutator
  linarith only [hDerivative]

/-- Original mixed degree/base remainder bound. One W/radius and two constants are
fixed before every parameter field, input, point and angular size. -/
theorem exists_retained_finite_degree_base_remainder_bound (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ KC KG : ℝ, 0 ≤ KC ∧ 0 ≤ KG ∧
      ∀ i j : Fin 3, ∀ T : R3 → Tpar, ∀ F : smoothCompactFiniteSphereCore hO hD,
      ∀ x X : R3, T x ∈ ParamRoom δ → DifferentiableAt ℝ T x →
      |GRAM i j (T x) (fderiv ℝ (Uin F) x X) (UBin F x)+
        GRAM i j (T x) (UBin F x) (fderiv ℝ (Uin F) x X)-
        fderiv ℝ (FIELD i j T F) x X| ≤
        KC*‖fderiv ℝ T x X‖*‖Uin F x‖^2+
        KG*‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖ := by
  have hGFull := ActualDegreeGramCancellation.exists_retained_degree_gram_cancellation_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hGFull with ⟨δG,hδG,hδG0,hδGρ,KG,hKG,hG⟩
  have hRoomFull := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hRoomFull with ⟨δC,Cm⟩
  have hCFull := ActualDegreeGramBaseDerivative.exists_actual_degree_gram_coefficient_derivative_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm.rev.pos Cm
  rcases hCFull with ⟨KC,hKC,hC⟩
  let δ := min δG δC
  have hδGle : δ ≤ δG := min_le_left _ _
  have hδCle : δ ≤ δC := min_le_right _ _
  have hSubG := commonRoom_mono y0 ρ hδGle
  have hSubC := commonRoom_mono y0 ρ hδCle
  refine ⟨δ,lt_min hδG Cm.rev.pos,hδGle.trans hδG0,hδGle.trans hδGρ,KC,KG,hKC,hKG,?_⟩
  intro i j T F x X ht hT
  have htG : T x ∈ ParamRoom δG := ⟨hSubG ht.1,ht.2⟩
  have htC : T x ∈ ParamRoom δC := ⟨hSubC ht.1,ht.2⟩
  have hi : DifferentiableAt ℝ (EH i) (T x) := (Cm.germHigh i _ htC).differentiableAt (by simp)
  have hj : DifferentiableAt ℝ (EH j) (T x) := (Cm.germHigh j _ htC).differentiableAt (by simp)
  have hDegree := ActualDegreeGramCancellation.finite_degree_input_inclusion hO hD F x
  have hDegreeD := finite_degree_derivative_inclusion hO hD F x X
  have hCommRaw := hG i j (T x) htG (Uin F x) (fderiv ℝ (Uin F) x X)
    (UBin F x) (fderiv ℝ (UBin F) x X) hDegree hDegreeD
  have hComm : |COMM i j T F x X| ≤ KG*‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖ := by
    unfold finiteDegreeGramCommutator
    exact hCommRaw
  have hCoef := hC i j (T x) htC (fderiv ℝ T x X) (Uin F x) (Uin F x) (UBin F x) hDegree
  have hIdentity := finite_degree_gram_base_signed_identity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j T F x X hi hj hT
  calc
    _ = |-COEF i j (T x) (fderiv ℝ T x X) (Uin F x) (UBin F x)-COMM i j T F x X| :=
      congrArg abs hIdentity
    _ ≤ |COEF i j (T x) (fderiv ℝ T x X) (Uin F x) (UBin F x)|+|COMM i j T F x X| := by
      simpa only [abs_neg] using abs_sub
        (-COEF i j (T x) (fderiv ℝ T x X) (Uin F x) (UBin F x)) (COMM i j T F x X)
    _ ≤ KC*‖fderiv ℝ T x X‖*‖Uin F x‖*‖Uin F x‖+
        KG*‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖ := add_le_add hCoef hComm
    _ = _ := by ring

/-- Original scalar degree Gram field is supported in the original finite input support,
even for an arbitrary parameter field. No coefficient regularity off support is assumed. -/
theorem hasCompactSupport_finiteDegreeGramField (i j : Fin 3) (T : R3 → Tpar)
    (F : smoothCompactFiniteSphereCore hO hD) : HasCompactSupport (FIELD i j T F) := by
  refine HasCompactSupport.intro F.property.2.1 ?_
  intro x hx
  have hZero : Uin F x=0 := by
    simpa only [ActualHigherSFormation.higherSInput] using
      ActualHigherSFormation.finiteCoreSobolevLift_eq_zero_of_eval hO hD (3/2 : ℝ) F x
        (ActualHigherSFormation.eval_eq_zero_of_notMem_tsupport hO hD F x hx)
  simp only [finiteDegreeGramField,ActualDegreeGramCancellation.degreeGram,hZero,map_zero,inner_zero_left]

local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Actual profile Gram scalar is globally smooth from the native membership-only
family glue. It needs room membership only on the original finite input support. -/
theorem contDiff_original_profile_degree_gram (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F, (Tq δr Ar p q) x ∈ ParamRoom δ) (i j : Fin 3) :
    ContDiff ℝ ∞ (FIELD i j (Tq δr Ar p q) F) := by
  have hU : ContDiff ℝ ∞ (Uin F) := by
    simpa only [ActualHigherSFormation.higherSInput] using contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hUB : ContDiff ℝ ∞ (UBin F) := by
    simpa only [ActualHigherSFormation.higherSDegreeInput] using
      contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F)
  have hU0 := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q F
  have hUB0 := ActualHigherSFormation.higherSDegreeInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q F
  have hLeft := ActualHigherSFormation.contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q (EH i) F
    (fun x hx => Cm.germHigh i _ (hT x hx)) (Uin F) hU hU0
  have hRight := ActualHigherSFormation.contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q (EH j) F
    (fun x hx => Cm.germHigh j _ (hT x hx)) (UBin F) hUB hUB0
  have hKLLeft := (KL).contDiff.comp hLeft
  have hKLRight := (KL).contDiff.comp hRight
  unfold finiteDegreeGramField ActualDegreeGramCancellation.degreeGram
  simpa only [Function.comp_apply] using hKLLeft.inner ℝ hKLRight

/-- Actual original profile specialization: all constants precede every profile and
finite input, with the unchanged beta/radius hypotheses and exact energy regularity. -/
theorem exists_retained_original_profile_degree_base_remainder_bound (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 → ∀ hAr : 0 < Ar, 1 ≤ p →
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ F : smoothCompactFiniteSphereCore hO hD, ∀ x X : R3,
      (Tq δr Ar p q) x ∈ ParamRoom δ → 1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
      ∀ i j : Fin 3,
      |GRAM i j ((Tq δr Ar p q) x) (fderiv ℝ (Uin F) x X) (UBin F x)+
        GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X)-
        fderiv ℝ (FIELD i j (Tq δr Ar p q) F) x X| ≤
        K*(‖X‖*‖Uin F x‖^2+‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖) := by
  have hRawFull := exists_retained_finite_degree_base_remainder_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hRawFull with ⟨δ,hδ,hδ0le,hδρ,KC,KG,hKC,hKG,hRaw⟩
  have hJetFull := exists_reference_radius_parameter_uniform_jet_bounds g hg L hL
    (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  rcases hJetFull with ⟨CT,hCTpos,hCT⟩
  have hCT0 : 0 ≤ CT := le_of_lt hCTpos
  let K := KC*CT+KG
  have hKCCT : 0 ≤ KC*CT := mul_nonneg hKC hCT0
  have hK : 0 ≤ K := add_nonneg hKCCT hKG
  have hCK : KC*CT ≤ K := le_add_of_nonneg_right hKG
  have hGK : KG ≤ K := le_add_of_nonneg_left hKCCT
  refine ⟨δ,hδ,hδ0le,hδρ,K,hK,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq F x X hx hβ hsmall i j
  have hxK : x ∈ closedBall y0 ρ := hx.1.2.1
  have hdR : ‖fderiv ℝ (referenceRadius δr Ar p L) x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx.2
  have hJet := hCT q hq δr hδr hδr1 Ar hAr p hp x hxK hβ hsmall hdR
  have hTnorm : ‖fderiv ℝ (Tq δr Ar p q) x‖ ≤ CT := by
    rw [← norm_iteratedFDeriv_one]
    exact hJet.2.1
  have hTDnorm : ‖fderiv ℝ (Tq δr Ar p q) x X‖ ≤ CT*‖X‖ :=
    (ContinuousLinearMap.le_opNorm (fderiv ℝ (Tq δr Ar p q) x) X).trans
      (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg X))
  have hTsmooth := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q
  have hTd : DifferentiableAt ℝ (Tq δr Ar p q) x := hTsmooth.differentiable (by simp) x
  have hPoint := hRaw i j (Tq δr Ar p q) F x X hx hTd
  have hFirst : KC*‖fderiv ℝ (Tq δr Ar p q) x X‖*‖Uin F x‖^2 ≤
      (KC*CT)*(‖X‖*‖Uin F x‖^2) := by
    calc
      _ ≤ KC*(CT*‖X‖)*‖Uin F x‖^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hTDnorm hKC) (sq_nonneg _)
      _ = _ := by ring
  have hP0 : 0 ≤ ‖X‖*‖Uin F x‖^2 := mul_nonneg (norm_nonneg X) (sq_nonneg _)
  have hZ0 : 0 ≤ ‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    _ ≤ KC*‖fderiv ℝ (Tq δr Ar p q) x X‖*‖Uin F x‖^2+
        KG*‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖ := hPoint
    _ ≤ (KC*CT)*(‖X‖*‖Uin F x‖^2)+KG*(‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖) := by
      exact add_le_add hFirst (le_of_eq (by ring))
    _ ≤ K*(‖X‖*‖Uin F x‖^2)+K*(‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖) :=
      add_le_add (mul_le_mul_of_nonneg_right hCK hP0) (mul_le_mul_of_nonneg_right hGK hZ0)
    _ = _ := by ring
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualDegreeGramBaseIdentity
