import Calderon.ActualLowerUSDLowFinitePairing
import Calderon.ActualLowerUSSecondRow
import Calderon.ActualLowerUSSecondRowDerivative
import Calderon.ActualLowerUSSignedRows
import Calderon.ActualHigherSScalarCommutatorNativeForm

/-! Delegated GPT-6.1 Sol; before code ../t-finite-domain-upfront-v001.md and
../t-weighted-ibp-upfront.md. Genuine actual T coefficient, supported weighted
IBP, original density-log correction and original reference-profile energy.
No finite physical S output, cap callback or author compiler job. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSTWeightedIBP
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualMixedAngularPairedGains ActualLowerUSSecondRow ActualLowerUSFirstOutput ActualLowerUSSignedRows
  ActualHigherSLeadingBracketGain ActualHigherSFirstPhysicalCommutatorGraph ActualHigherSFirstCoefficientJets
  ActualHigherSPhysicalPairing ActualHigherSScalarCommutatorForm ActualHigherSScalarCommutatorNativeForm
  ActualHigherSScalarCommutatorCoefficients
  ActualNormalizedSecondDriftDefectWeightedJets PrincipalCommutator ReferenceDensityBounds
  ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  FixedParameterProfilePullback FixedParameterProfileBudgets

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

@[instance_reducible] private def tLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] tLowNormed
@[instance_reducible] private def tLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] tLowSpace
@[instance_reducible] private def tDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] tDualNormed
@[instance_reducible] private def tDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] tDualSpace
@[instance_reducible] private def tPairNormed : NormedAddCommGroup (Half →L[ℝ] Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] tPairNormed
@[instance_reducible] private def tPairSpace : NormedSpace ℝ (Half →L[ℝ] Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] tPairSpace

private theorem density_pairing_regroup (m ell dm : ℝ) (hm : m*ell=dm)
    (u du v : Half) (T dT : Half →L[ℝ] Neg) :
    dm*PP u (T v)+m*PP du (T v)+m*PP u (dT v) =
      m*PP du (T v)+m*PP u ((dT+ell•T) v) := by
  simp only [add_apply,smul_apply,sphereSobolevDualPairing,inner_add_right,real_inner_smul_right]
  rw [← hm]
  ring

private theorem normalize_low_graph
    (T D : Half →L[ℝ] Neg) (P Pnew : Hi →L[ℝ] Half)
    (Q Qnew : Half →L[ℝ] Neg) (DH : Hi →L[ℝ] Half)
    (u : Hi) (f df : Half) (hP : P=Pnew) (hQ : Q=Qnew)
    (hI : IH u=f) (hD : DH u=df)
    (h : T (IH u)=D (P u)-Q (DH u)) : T f=D (Pnew u)-Qnew df := by
  rw [← hI,← hP,← hQ,← hD]
  exact h

private theorem pairing_sub_value (u : Half) (v z : Neg) :
    PP u (v-z)=PP u v-PP u z := inner_sub_right _ _ _

/-- Transport a proved scalar row dictionary through two finite integrable sums. -/
private theorem integral_eq_sum_sum_of_pointwise
    (f : R3 → ℝ) (row : Fin 3 → Fin 3 → R3 → ℝ)
    (hrow : ∀ i j, Integrable (row i j))
    (hpoint : ∀ x, f x = ∑ i : Fin 3, ∑ j : Fin 3, row i j x) :
    (∫ x, f x) = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, row i j x := by
  calc
    _ = ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, row i j x :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∑ i : Fin 3, ∫ x, ∑ j : Fin 3, row i j x :=
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hrow i j))
    _ = _ := Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hrow i j))

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)

local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "TC" => lowerUSSecondCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

variable (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
  (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "LF" => finiteCoreSobolevLift hO hD (1/2 : ℝ)
local notation "LH" => finiteCoreSobolevLift hO hD (3/2 : ℝ)
local notation "dd" => (fun i : Fin 3 => coreDirectionalDerivative hO hD (coordinateDirection i))
local notation "DD" => nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "BN" => (fun i : Fin 3 => nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr)
local notation "PH" => highFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "PL" => canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "PO" => nativeFirstOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "NT" => nativeTSecondDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 dr Ar p hdr hAr q
local notation "mu" => (fun x : R3 => referenceDensityFamily g L (q,x))
local notation "ell" => (fun (i : Fin 3) (x : R3) => referenceDensityLogCoordinateJoint g L i (q,x))

private lemma tHalf_eq_halfInput (F : FC) : LF F = halfInput hO hD F := by
  funext x
  exact (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) F x).symm

private lemma tHalf_zero_off (F : FC) (x : R3) (hx : x ∉ tsupport F.val) : LF F x = 0 := by
  rw [tHalf_eq_halfInput hO hD F]
  exact halfInput_eq_zero_off hO hD F x hx

/-- Literal gradient term; the ordered i,j are not symmetrized. -/
def nativeTGradientDensity (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (F : FC) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    PP (directionalFDeriv (coordinateDirection i) (LF F) x)
      (TC mixed δ gen g2 q dr Ar p i j x
        (directionalFDeriv (coordinateDirection j) (LF F) x))

/-- Actual coefficient derivative PLUS original logarithmic-density derivative. -/
def nativeTCorrectionDensity (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (F : FC) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    PP (LF F x)
      ((directionalFDeriv (coordinateDirection i) (TC mixed δ gen g2 q dr Ar p i j) x +
          ell i x • TC mixed δ gen g2 q dr Ar p i j x)
        (directionalFDeriv (coordinateDirection j) (LF F) x))

private lemma tRow_graph_pairing (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (δc : ℝ) (Cm : CRoom δc) (i j : Fin 3) (U V : FC) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (htD : (Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (htC : (Tq dr Ar p q) x ∈ ParamRoom δc) :
    ⟪-(BN i U).val x,PO j V x⟫_ℝ - ⟪U.val x,PO j (DD i V) x⟫_ℝ =
      PP (LF U x) (TC mixed δ gen g2 q dr Ar p i j x (LF V x)) := by
  have hMap := lowerUSSecondCoefficient_graph_of_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ gen g2 q dr Ar p i j x htG htM htD (LH V x)
  have hPH : PH x j = (referenceRadius dr Ar p L x)^2 •
      ∑ b : Fin 3, firstCoordinateWeight g g2 L j b ((Tq dr Ar p q) x) •
        canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 b ((Tq dr Ar p q) x) := by
    unfold highFirstCoordinateCoefficient
    exact congrArg (fun A : Hi →L[ℝ] Half => (referenceRadius dr Ar p L x)^2 • A)
      (highFirstCoordinateFactor_eq_contracted
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 j ((Tq dr Ar p q) x))
  have hPL : PL x j = (referenceRadius dr Ar p L x)^2 •
      ∑ b : Fin 3, firstCoordinateWeight g g2 L j b ((Tq dr Ar p q) x) •
        canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 b ((Tq dr Ar p q) x) := by
    unfold canonicalFirstCoordinateCoefficient
    exact congrArg (fun A : Half →L[ℝ] Neg => (referenceRadius dr Ar p L x)^2 • A)
      (firstCoordinateFactor_eq_contracted
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 j ((Tq dr Ar p q) x))
  have hInput : IH (LH V x) = LF V x :=
    sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) V x
  have hDHigh : lowerAdjointFirstHigh g L hF hO hD g2 q dr Ar p i x (LH V x) =
      LF (DD i V) x :=
    lowerAdjointFirstHigh_finiteCore_graph hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i V x
  have hMap' := normalize_low_graph (TC mixed δ gen g2 q dr Ar p i j x)
    (lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p i x)
    _ (PH x j) _ (PL x j) (lowerAdjointFirstHigh g L hF hO hD g2 q dr Ar p i x)
    (LH V x) (LF V x) (LF (DD i V) x) hPH.symm hPL.symm hInput hDHigh hMap
  have hFirst : PP (LF U x)
      (lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p i x (PH x j (LH V x))) =
      ⟪-(BN i U).val x,PO j V x⟫_ℝ := by
    have hDPair := nativeDlow_finite_pairing hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr i U x (PH x j (LH V x))
    have hp := finiteCore_halfPairing_eq_inner hO hD ((-BN i) U) (PH x j (LH V x)) x
    simp only [sphereSobolevInclusionL_finiteCoreSobolevLift,LinearMap.neg_apply,
      Submodule.coe_neg,Pi.neg_apply] at hDPair hp
    have hOut : PO j V x = sphereSobolevHalfToSphereL2L hO hD (PH x j (LH V x)) := by
      simp only [ActualLowerUSFirstOutput.nativeFirstOut]
    have hOutPair := congrArg (fun z : SphereL2 => ⟪-(BN i U).val x,z⟫_ℝ) hOut
    have hCombined := Eq.trans hDPair hp
    have hResult := Eq.trans hCombined (Eq.symm hOutPair)
    exact hResult
  have hSecond : PP (LF U x) (PL x j (LF (DD i V) x)) = ⟪U.val x,PO j (DD i V) x⟫_ℝ := by
    have hgP := highFirstCoordinateCoefficient_negative_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δc Cm g2 dr Ar p q j x htC (LH (DD i V) x)
    have hp := finiteCore_halfPairing_eq_inner hO hD U (PH x j (LH (DD i V) x)) x
    simp only [sphereSobolevInclusionL_finiteCoreSobolevLift] at hp hgP
    have hOut : PO j (DD i V) x =
        sphereSobolevHalfToSphereL2L hO hD (PH x j (LH (DD i V) x)) := by
      simp only [ActualLowerUSFirstOutput.nativeFirstOut]
    have hOutPair := congrArg (fun z : SphereL2 => ⟪U.val x,z⟫_ℝ) hOut
    have hBack := Eq.symm (congrArg (fun z : Neg => PP (LF U x) z) hgP)
    have hCombined := Eq.trans hBack hp
    have hResult := Eq.trans hCombined (Eq.symm hOutPair)
    exact hResult
  have hSubtract := pairing_sub_value (LF U x)
    (lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p i x (PH x j (LH V x)))
    (PL x j (LF (DD i V) x))
  have hPhysicalValues := congrArg₂ (fun a b : ℝ => a-b) hFirst hSecond
  have hValues := Eq.trans hSubtract hPhysicalValues
  have hPairMap := congrArg (fun z : Neg => PP (LF U x) z) hMap'
  have hResult := Eq.symm (Eq.trans hPairMap hValues)
  simpa only using hResult

/-- Exact physical T density dictionary on the retained rooms. -/
theorem nativeTSecondDensity_eq_coefficient (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (δc : ℝ) (Cm : CRoom δc) (F : FC) (x : R3)
    (hRooms : x ∈ tsupport F.val →
      (Tq dr Ar p q) x ∈ ParamRoom δ ∧ (Tq dr Ar p q) x ∈ ParamRoom mixed.δ ∧
      (Tq dr Ar p q) x ∈ ParamRoom data.δ ∧ (Tq dr Ar p q) x ∈ ParamRoom δc) :
    NT F x = ∑ i : Fin 3, ∑ j : Fin 3,
      PP (LF F x) (TC mixed δ gen g2 q dr Ar p i j x
        (directionalFDeriv (coordinateDirection i)
          (directionalFDeriv (coordinateDirection j) (LF F)) x)) := by
  by_cases hx : x ∈ tsupport F.val
  · obtain ⟨htG,htM,htD,htC⟩ := hRooms hx
    unfold nativeTSecondDensity
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hd : directionalFDeriv (coordinateDirection i)
        (directionalFDeriv (coordinateDirection j) (LF F)) x = LF ((dd i) ((dd j) F)) x := by
      have hFun : directionalFDeriv (coordinateDirection j) (LF F) = LF ((dd j) F) :=
        funext (directionalFDeriv_finiteCoreSobolevLift hO hD (1/2 : ℝ) F (coordinateDirection j))
      rw [hFun,directionalFDeriv_finiteCoreSobolevLift]
    rw [hd]
    exact tRow_graph_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q mixed δ gen δc Cm i j F ((dd i) ((dd j) F)) x htG htM htD htC
  · have hzF : F.val x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hzB (i : Fin 3) : (BN i F).val x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hx (finiteCoreSupportPreserving_nativeB hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i F hh))
    simp only [nativeTSecondDensity,hzF,hzB,neg_zero,inner_zero_left,sub_self,
      Finset.sum_const_zero,tHalf_zero_off hO hD F x hx,sphereSobolevDualPairing]

local notation "TG" => nativeTGradientDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q
local notation "TR" => nativeTCorrectionDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q

/-- Separate integrability and exact weighted IBP for the original physical T. -/
def NativeTWeightedIdentity (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (F : FC) : Prop :=
  Integrable (fun x => mu x * NT F x) ∧
  Integrable (fun x => mu x * TG mixed δ gen F x) ∧
  Integrable (fun x => mu x * TR mixed δ gen F x) ∧
  (∫ x, mu x * NT F x) =
    -(∫ x, mu x * TG mixed δ gen F x) - ∫ x, mu x * TR mixed δ gen F x

/-- Supported smoothness, not global coefficient smoothness, suffices. These
actual room/smoothness premises are discharged internally by the profile factory. -/
theorem nativeTWeightedIdentity_of_support
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (δc : ℝ) (Cm : CRoom δc) (F : FC)
    (hRooms : ∀ x ∈ tsupport F.val,
      (Tq dr Ar p q) x ∈ ParamRoom δ ∧ (Tq dr Ar p q) x ∈ ParamRoom mixed.δ ∧
      (Tq dr Ar p q) x ∈ ParamRoom data.δ ∧ (Tq dr Ar p q) x ∈ ParamRoom δc)
    (hTC : ∀ x ∈ tsupport F.val, ∀ i j : Fin 3,
      ContDiffAt ℝ ∞ (TC mixed δ gen g2 q dr Ar p i j) x) :
    NativeTWeightedIdentity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q mixed δ gen F := by
  let u := LF F
  let K := tsupport F.val
  let A : Fin 3 → Fin 3 → R3 → ℝ := fun i j x => mu x * PP (u x)
    (TC mixed δ gen g2 q dr Ar p i j x
      (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) x))
  let G : Fin 3 → Fin 3 → R3 → ℝ := fun i j x => mu x *
    PP (directionalFDeriv (coordinateDirection i) u x)
      (TC mixed δ gen g2 q dr Ar p i j x (directionalFDeriv (coordinateDirection j) u x))
  let R : Fin 3 → Fin 3 → R3 → ℝ := fun i j x => mu x * PP (u x)
    ((directionalFDeriv (coordinateDirection i) (TC mixed δ gen g2 q dr Ar p i j) x +
      ell i x • TC mixed δ gen g2 q dr Ar p i j x)
      (directionalFDeriv (coordinateDirection j) u x))
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD (1/2 : ℝ) F
  have hu0 : ∀ x ∉ K, u x=0 := tHalf_zero_off hO hD F
  have hK : IsCompact K := F.property.2.1
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hv (j : Fin 3) := contDiff_directionalFDeriv (coordinateDirection j) u hu
  have hv0 (j : Fin 3) : ∀ x ∉ K, directionalFDeriv (coordinateDirection j) u x=0 :=
    fun x hx => directional_eq_zero_off u K hK.isClosed hu0 (coordinateDirection j) x hx
  have hAi (i j : Fin 3) : Integrable (A i j) := by
    exact integrable_weighted_supported_operator_pair halfDualPairingL mu u
      (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u))
      (TC mixed δ gen g2 q dr Ar p i j) K hK hm.continuous hu.continuous
      (contDiff_directionalFDeriv (coordinateDirection i) _ (hv j))
      (fun x hx => directional_eq_zero_off _ K hK.isClosed (hv0 j) (coordinateDirection i) x hx)
      (fun x hx => hTC x hx i j)
  have hGi (i j : Fin 3) : Integrable (G i j) :=
    integrable_weighted_supported_operator_pair halfDualPairingL mu
      (directionalFDeriv (coordinateDirection i) u) (directionalFDeriv (coordinateDirection j) u)
      (TC mixed δ gen g2 q dr Ar p i j) K hK hm.continuous (hv i).continuous
      (hv j) (hv0 j) (fun x hx => hTC x hx i j)
  have hRi (i j : Fin 3) : Integrable (R i j) := by
    have he : ContDiff ℝ ∞ (ell i) :=
      (contDiff_referenceDensityLogCoordinateJoint g hg L i).comp (contDiff_const.prodMk contDiff_id)
    exact integrable_weighted_supported_operator_pair halfDualPairingL mu u
      (directionalFDeriv (coordinateDirection j) u)
      (fun x => directionalFDeriv (coordinateDirection i) (TC mixed δ gen g2 q dr Ar p i j) x +
        ell i x • TC mixed δ gen g2 q dr Ar p i j x)
      K hK hm.continuous hu.continuous (hv j) (hv0 j)
      (fun x hx => (contDiffAt_directional _ x (coordinateDirection i) (hTC x hx i j)).add
        (he.contDiffAt.smul (hTC x hx i j)))
  have hRow (i j : Fin 3) : (∫ x, A i j x) = -(∫ x, G i j x) - ∫ x, R i j x := by
    have hBase := weighted_second_operator_green halfDualPairingL mu u
      (TC mixed δ gen g2 q dr Ar p i j) K hK hm hu hu0
      (fun x hx => hTC x hx i j) (coordinateDirection i) (coordinateDirection j)
    have hPoint (x : R3) :
        directionalFDeriv (coordinateDirection i) mu x * PP (u x)
            (TC mixed δ gen g2 q dr Ar p i j x (directionalFDeriv (coordinateDirection j) u x)) +
          mu x * PP (directionalFDeriv (coordinateDirection i) u x)
            (TC mixed δ gen g2 q dr Ar p i j x (directionalFDeriv (coordinateDirection j) u x)) +
          mu x * PP (u x)
            (directionalFDeriv (coordinateDirection i) (TC mixed δ gen g2 q dr Ar p i j) x
              (directionalFDeriv (coordinateDirection j) u x)) = G i j x + R i j x := by
      have hDensity : mu x * ell i x = directionalFDeriv (coordinateDirection i) mu x := by
        dsimp only
        rw [referenceDensityLogCoordinateJoint_eq_slice,← mul_assoc,
          mul_inv_cancel₀ (referenceDensityFamily_pos g hg L (q,x)).ne',one_mul]
      dsimp only [G,R]
      exact density_pairing_regroup (mu x) (ell i x)
        (directionalFDeriv (coordinateDirection i) mu x) hDensity
        (u x) (directionalFDeriv (coordinateDirection i) u x)
        (directionalFDeriv (coordinateDirection j) u x)
        (TC mixed δ gen g2 q dr Ar p i j x)
        (directionalFDeriv (coordinateDirection i) (TC mixed δ gen g2 q dr Ar p i j) x)
    have hInt : (∫ x, directionalFDeriv (coordinateDirection i) mu x * PP (u x)
          (TC mixed δ gen g2 q dr Ar p i j x (directionalFDeriv (coordinateDirection j) u x)) +
        mu x * PP (directionalFDeriv (coordinateDirection i) u x)
          (TC mixed δ gen g2 q dr Ar p i j x (directionalFDeriv (coordinateDirection j) u x)) +
        mu x * PP (u x)
          (directionalFDeriv (coordinateDirection i) (TC mixed δ gen g2 q dr Ar p i j) x
            (directionalFDeriv (coordinateDirection j) u x))) =
        (∫ x, G i j x) + ∫ x, R i j x :=
      (integral_congr_ae (Eventually.of_forall hPoint)).trans (integral_add (hGi i j) (hRi i j))
    simp only [halfDualPairingL_apply] at hBase
    change (∫ x, A i j x) = -_ at hBase
    rw [hInt] at hBase
    exact hBase.trans (by ring)
  have hNPoint (x : R3) : mu x * NT F x = ∑ i : Fin 3, ∑ j : Fin 3, A i j x := by
    rw [nativeTSecondDensity_eq_coefficient g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 Room hreg data g2 hg2 dr Ar p hdr hAr q mixed δ gen δc Cm F x (hRooms x)]
    simp only [A,u,Finset.mul_sum]
  have hGPoint (x : R3) : mu x * TG mixed δ gen F x = ∑ i : Fin 3, ∑ j : Fin 3, G i j x := by
    simp only [nativeTGradientDensity,G,u,Finset.mul_sum]
  have hRPoint (x : R3) : mu x * TR mixed δ gen F x = ∑ i : Fin 3, ∑ j : Fin 3, R i j x := by
    simp only [nativeTCorrectionDensity,R,u,Finset.mul_sum]
  have hNInt := (integrable_finsetSum (Finset.univ : Finset (Fin 3))
    (fun i _ => integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hAi i j))).congr
      (Eventually.of_forall (fun x => (hNPoint x).symm))
  have hGInt := (integrable_finsetSum (Finset.univ : Finset (Fin 3))
    (fun i _ => integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hGi i j))).congr
      (Eventually.of_forall (fun x => (hGPoint x).symm))
  have hRInt := (integrable_finsetSum (Finset.univ : Finset (Fin 3))
    (fun i _ => integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hRi i j))).congr
      (Eventually.of_forall (fun x => (hRPoint x).symm))
  refine ⟨hNInt,hGInt,hRInt,?_⟩
  have hNI : (∫ x, mu x * NT F x) = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, A i j x := by
    rw [integral_congr_ae (Eventually.of_forall hNPoint),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hAi i j))]
    exact Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hAi i j))
  have hGI : (∫ x, mu x * TG mixed δ gen F x) = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, G i j x := by
    rw [integral_congr_ae (Eventually.of_forall hGPoint),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hGi i j))]
    exact Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hGi i j))
  have hRI : (∫ x, mu x * TR mixed δ gen F x) = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, R i j x := by
    rw [integral_congr_ae (Eventually.of_forall hRPoint),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hRi i j))]
    exact Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hRi i j))
  rw [hNI,hGI,hRI]
  simp only [hRow,Finset.sum_sub_distrib,Finset.sum_neg_distrib]

/-- Actual fixed-g2 producer: all coefficient caps, density corrections,
rooms and reference-energy comparison are selected internally, before profiles. -/
theorem exists_nativeTSecond_uniform_profile_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ mixed : MRoom, ∃ δ : ℝ, 0 < δ ∧ ∃ gen : GRoom δ,
    ∃ CT : ℝ, 0 < CT ∧ ∃ etaT : ℝ, 0 < etaT ∧ etaT ≤ data.eta0 ∧ etaT ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaT →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta * referenceRadius dr Ar p L x) →
      NativeTWeightedIdentity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q mixed δ gen F ∧
      |∫ x, referenceDensityFamily g L (q,x) * nativeTSecondDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 dr Ar p hdr hAr q F x| ≤
        CT * eta * ∫ x, referenceDensityFamily g L (q,x) *
          finiteCoreReferenceProfileEnergy hO hD g hg L q
            (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨mixed,δ,hδ,gen,CV,hCV,etaV,hEtaV,hEtaV0,hEtaV1,hValue⟩ :=
    exists_retained_secondRow_uniform_profile_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨CD,hCD,etaD,hEtaD,hEtaD0,hEtaD1,hDerivative⟩ :=
    exists_lowerUSSecondCoefficient_uniform_derivative_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ hδ gen g2 hg2 hL
  obtain ⟨δc,Cm,_hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨etaRoom,hEtaRoom,_hEtaRoom1,hGuard⟩ :=
    exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ δc Cm.rev.pos
      (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨M,hM,hDensity⟩ := exists_density_coordinate_relative_bound
    g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨Cref,hCref,hReference⟩ := exists_halfInput_coordinate_reference_integral_bound
    hO hD g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Q : ℝ := CV+CD+1
  let A : ℝ := ‖(halfDualPairingL : Half →L[ℝ] Neg →L[ℝ] ℝ)‖*Q*(M+3)
  let Ctotal : ℝ := 9*A*Cref+1
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hTotal : 0 < Ctotal := by dsimp only [Ctotal]; positivity
  refine ⟨mixed,δ,hδ,gen,Ctotal,hTotal,min etaV (min etaD etaRoom),
    lt_min hEtaV (lt_min hEtaD hEtaRoom),(min_le_left _ _).trans hEtaV0,
    (min_le_left _ _).trans hEtaV1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaT K _hK hBall F hSupp hb hs hH8
  let muq : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta : R3 → ℝ := actualReferenceBeta g L q dr Ar p
  let u := finiteCoreSobolevLift hO hD (1/2 : ℝ) F
  let N := nativeTSecondDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 dr Ar p hdr hAr q F
  let Cij : Fin 3 → Fin 3 → R3 → Half →L[ℝ] Neg := TC mixed δ gen g2 q dr Ar p
  let S := tsupport F.val
  have hEtaV' : eta ≤ etaV := hetaT.trans (min_le_left _ _)
  have hEtaD' : eta ≤ etaD := hetaT.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hEtaRoom' : eta ≤ etaRoom := hetaT.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hClosed (x : R3) (hx : x ∈ S) : x ∈ closedBall y0 ρ :=
    ball_subset_closedBall (hBall (hSupp hx))
  have hV (x : R3) (hx : x ∈ S) := hValue q hq dr hdr hdr1 Ar hAr p hp eta heta hEtaV'
    x (hClosed x hx) (hBall (hSupp hx)) (hb x (hSupp hx)) (hs x (hSupp hx)) (hH8 x (hSupp hx))
  have hDeriv (x : R3) (hx : x ∈ S) (i j : Fin 3) := hDerivative q hq dr hdr hdr1 Ar hAr p hp
    eta heta hEtaD' x (hClosed x hx) (hBall (hSupp hx)) (hb x (hSupp hx))
    (hH8 x (hSupp hx)) (hs x (hSupp hx)) i j
  have hRooms (x : R3) (hx : x ∈ S) :
      (Tq dr Ar p q) x ∈ ParamRoom δ ∧ (Tq dr Ar p q) x ∈ ParamRoom mixed.δ ∧
      (Tq dr Ar p q) x ∈ ParamRoom data.δ ∧ (Tq dr Ar p q) x ∈ ParamRoom δc := by
    have hgRoom := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta hEtaRoom'
      x (hClosed x hx) (hBall (hSupp hx)) (hb x (hSupp hx)) (hs x (hSupp hx))
    exact ⟨(hV x hx).1,(hV x hx).2.1,(hV x hx).2.2.1,
      (higherSParam_eventually_mem y0 ρ δc L dr Ar q p hdr hAr x hgRoom).self_of_nhds⟩
  have hIdentity := nativeTWeightedIdentity_of_support
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q mixed δ gen δc Cm F hRooms
    (fun x hx i j => (hDeriv x hx i j).1)
  refine ⟨hIdentity,?_⟩
  have hmu : ContDiff ℝ ∞ muq :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hbeta := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hbetaPos := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD (1/2 : ℝ) F
  have hU0 : ∀ x ∉ S, u x=0 := tHalf_zero_off hO hD F
  have hQCV : CV ≤ Q := by dsimp only [Q]; linarith
  have hQCD : CD ≤ Q := by dsimp only [Q]; linarith
  have hRows (i j : Fin 3) := weighted_second_operator_form_bound halfDualPairingL muq beta u
    (Cij i j) S F.property.2.1 hmu hbeta hbetaPos hu hU0
    (fun x hx => (hDeriv x hx i j).1) Q M eta hQ.le (zero_le_one.trans hM) heta
    (fun x => (referenceDensityFamily_pos g hg L (q,x)).le)
    (fun x hx => hb x (hSupp hx)) i j
    (fun x hx => ((hV x hx).2.2.2 i j).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hQCV heta) (hbetaPos x).le))
    (fun x hx => by
      have hEval := (fderiv ℝ (Cij i j) x).le_opNorm (coordinateDirection i)
      have hDir : ‖directionalFDeriv (coordinateDirection i) (Cij i j) x‖ ≤
          ‖fderiv ℝ (Cij i j) x‖ := by
        simpa only [directionalFDeriv,ActualScalarPrincipalAdjoint.norm_coordinateDirection,mul_one] using hEval
      exact hDir.trans ((hDeriv x hx i j).2.trans (mul_le_mul_of_nonneg_right hQCD heta)))
    (fun x hx => hDensity q hq x (hClosed x hx) i)
  have hNPoint (x : R3) : muq x * N x = ∑ i : Fin 3, ∑ j : Fin 3,
      muq x * halfDualPairingL (u x)
        (Cij i j x (directionalFDeriv (coordinateDirection i)
          (directionalFDeriv (coordinateDirection j) u) x)) := by
    have hh := nativeTSecondDensity_eq_coefficient g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 Room hreg data g2 hg2 dr Ar p hdr hAr q mixed δ gen δc Cm F x (hRooms x)
    dsimp only [N,muq,u,Cij]
    rw [hh]
    simp only [Finset.mul_sum,halfDualPairingL_apply]
  have hNI : (∫ x, muq x * N x) = ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x, muq x * halfDualPairingL (u x)
        (Cij i j x (directionalFDeriv (coordinateDirection i)
          (directionalFDeriv (coordinateDirection j) u) x)) := by
    exact integral_eq_sum_sum_of_pointwise (fun x => muq x * N x)
      (fun i j x => muq x * halfDualPairingL (u x)
        (Cij i j x (directionalFDeriv (coordinateDirection i)
          (directionalFDeriv (coordinateDirection j) u) x)))
      (fun i j => (hRows i j).1) hNPoint
  have hBound : |∫ x, muq x * N x| ≤ (9*A*eta)*ActualScalarPrincipalSelfFormBound.coordinateEnergy coordinateDirection muq beta u := by
    rw [hNI]
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          |∫ x, muq x * halfDualPairingL (u x)
            (Cij i j x (directionalFDeriv (coordinateDirection i)
              (directionalFDeriv (coordinateDirection j) u) x))| := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (A*eta)*ActualScalarPrincipalSelfFormBound.coordinateEnergy coordinateDirection muq beta u :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (hRows i j).2))
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hRef := hReference q hq dr Ar p hdr hAr hp F
    (fun x hx => hClosed x hx) (fun x hx => hb x (hSupp hx))
  rw [← tHalf_eq_halfInput hO hD F] at hRef
  have hEnergyNonneg : 0 ≤ ∫ x, muq x *
      finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x :=
    integral_nonneg (fun x => mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbetaPos x).le F x))
  calc
    _ ≤ (9*A*eta)*ActualScalarPrincipalSelfFormBound.coordinateEnergy coordinateDirection muq beta u := hBound
    _ ≤ (9*A*eta)*(Cref*∫ x, muq x *
        finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x) :=
      mul_le_mul_of_nonneg_left hRef (by positivity)
    _ ≤ _ := by
      dsimp only [Ctotal]
      nlinarith [mul_nonneg heta hEnergyNonneg]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSTWeightedIBP
