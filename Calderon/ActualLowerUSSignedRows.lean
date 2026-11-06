import Calderon.ActualLowerUSFirstOutputLinearity
import Calderon.ActualLowerUSAdjointZeroSphereAdjoint
import Calderon.ActualLowerUSWeightedDomainBridge
import Calderon.ActualLowerUSDQDensity
import Calderon.FiniteCoreSobolevDerivativeEnergy

/-!
Author: GPT-6.1 Sol. Before-code ../lower-u-s-signed-rows-upfront.md.
Actual native signed lower U/S rows: full physical P/Q outputs and genuine
finite pretests, with no application of finite LA to a physical S output.
Author source; Root owns diagnostics, qualification and semantic acceptance.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSignedRows
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualPiJacobiRadialGainedRows ActualMixedAngularPairedGains
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualLowerUSFirstOutput ActualHigherSFirstPhysicalCommutatorGraph
  ActualHigherSZeroPhysicalGraph ActualLowerUSZeroAngularSum ActualLowerUSGainedDQ
  ActualModelCommutatorWords ActualHigherSZeroScalarCommutatorForm
  ActualHigherSScalarCommutatorForm PrincipalCommutator
  FixedParameterProfilePullback FixedParameterProfileBudgets ActualModelSMixedComparison

private theorem contDiff_halfToSphereL2_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (u : R3 → SphereSobolev (1/2 : ℝ)) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun x => sphereSobolevHalfToSphereL2L hO hD (u x)) :=
  (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hu

private theorem integral_fintype_sum_add_sub {ι : Type*} [Fintype ι]
    (f : ι → R3 → ℝ) (g h : R3 → ℝ)
    (hf : ∀ i, Integrable (f i)) (hg : Integrable g) (hh : Integrable h) :
    (∑ i : ι, ∫ x, f i x)+(∫ x, g x)-(∫ x, h x) =
      ∫ x, (∑ i : ι, f i x)+g x-h x := by
  have hsum : Integrable (fun x => ∑ i : ι, f i x) :=
    integrable_finsetSum (Finset.univ : Finset ι) (fun i _ => hf i)
  have hI : (∫ x, ∑ i : ι, f i x) = ∑ i : ι, ∫ x, f i x :=
    integral_finsetSum (Finset.univ : Finset ι) (fun i _ => hf i)
  have hA : (∫ x, (∑ i : ι, f i x)+g x) = (∫ x, ∑ i : ι, f i x)+(∫ x, g x) :=
    integral_add hsum hg
  have hS : (∫ x, ((∑ i : ι, f i x)+g x)-h x) =
      (∫ x, (∑ i : ι, f i x)+g x)-(∫ x, h x) :=
    integral_sub (hsum.add hg) hh
  calc
    _ = (∫ x, ∑ i : ι, f i x)+(∫ x, g x)-(∫ x, h x) :=
      congrArg (fun z : ℝ => z+(∫ x, g x)-(∫ x, h x)) hI.symm
    _ = (∫ x, (∑ i : ι, f i x)+g x)-(∫ x, h x) :=
      congrArg (fun z : ℝ => z-(∫ x, h x)) hA.symm
    _ = _ := hS.symm

/-- Abstract vector data only, used to isolate finite scalar algebra from
large actual native constructor terms. -/
private structure SignedRowData where
  test : SphereL2
  dtest : Fin 3 → SphereL2
  jtest : SphereL2
  p : Fin 3 → SphereL2
  q : SphereL2
  pp : Fin 3 → Fin 3 → SphereL2
  dp : Fin 3 → Fin 3 → SphereL2
  pd : Fin 3 → Fin 3 → SphereL2
  po : Fin 3 → Fin 3 → SphereL2
  dq : Fin 3 → SphereL2
  qd : Fin 3 → SphereL2
  pq : Fin 3 → SphereL2
  qp : Fin 3 → SphereL2
  pj : Fin 3 → SphereL2
  qj : SphereL2

private def signedRowRaw (d : SignedRowData) : ℝ :=
  (∑ i : Fin 3, ⟪d.dtest i,(∑ j : Fin 3, (d.dp i j+d.pp i j))+d.dq i+d.qd i⟫_ℝ)+
    ⟪d.jtest,(∑ j : Fin 3, d.p j)+d.q⟫_ℝ-
    ⟪d.test,((∑ i : Fin 3, ∑ j : Fin 3, d.pd i j)+
      (∑ i : Fin 3, ∑ j : Fin 3, d.po i j))+
      (∑ i : Fin 3, d.pq i)+(∑ i : Fin 3, d.pj i)+
      (∑ i : Fin 3, d.qp i)+d.qj⟫_ℝ

private def signedRowGrouped (d : SignedRowData) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, (⟪d.dtest i,d.pp i j⟫_ℝ-⟪d.test,d.pd i j⟫_ℝ))+
  (∑ j : Fin 3,
    ((∑ i : Fin 3, (⟪d.dtest i,d.dp i j⟫_ℝ-⟪d.test,d.po i j⟫_ℝ))+
    (⟪d.dtest j,d.qd j⟫_ℝ-⟪d.test,d.qp j⟫_ℝ)+
    (⟪d.jtest,d.p j⟫_ℝ-⟪d.test,d.pj j⟫_ℝ)))+
  ((∑ i : Fin 3, (⟪d.dtest i,d.dq i⟫_ℝ-⟪d.test,d.pq i⟫_ℝ))+
    (⟪d.jtest,d.q⟫_ℝ-⟪d.test,d.qj⟫_ℝ))

private theorem signedRowRaw_eq_grouped (d : SignedRowData) :
    signedRowRaw d = signedRowGrouped d := by
  simp only [signedRowRaw,signedRowGrouped,Fin.sum_univ_three,inner_add_right]
  ring

private lemma modelFirstOrder_base_expand {R : Type*} [Ring R]
    (d D : Fin 3 → R) (J : R) (j : Fin 3) :
    d j * modelFirstOrder d D J =
      (∑ i : Fin 3, (coefficientDerivative (d j) (D i)*d i+D i*(d j*d i)))+
      coefficientDerivative (d j) J+J*d j := by
  simp only [modelFirstOrder,coefficientDerivative,ActualModelCommutatorWords.commutator,
    Fin.sum_univ_three]
  noncomm_ring

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
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q




variable (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
  (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "dd" => (fun i : Fin 3 => coreDirectionalDerivative hO hD (coordinateDirection i))
local notation "D" => nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "Bnative" => (fun i : Fin 3 => nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr)
local notation "J" => nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "Js" => nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "LA" => nativeULowerAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "Pout" => nativeFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "Qout" => nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
local notation "SO" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q
  hreg data.δ0 data.germs g2
local notation "mu" => (fun x : R3 => referenceDensityFamily g L (q,x))
local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "Lo" => nativeULowerSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 dr Ar p hdr hAr q

/-- Actual coefficient derivative of Pout, retaining the full physical field. -/
def nativeDerivativePOutput (i j : Fin 3) (F : FC) (x : R3) : SphereL2 :=
  directionalFDeriv (coordinateDirection i) (Pout j F) x-Pout j ((dd i) F) x

/-- Actual coefficient derivative of Qout, retaining the full physical field. -/
def nativeDerivativeQOutput (i : Fin 3) (F : FC) (x : R3) : SphereL2 :=
  directionalFDeriv (coordinateDirection i) (Qout F) x-Qout ((dd i) F) x

/-- Literal second-base coefficient density, with genuine Dstar=-B. -/
def nativeTSecondDensity (F : FC) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (⟪-(Bnative i F).val x,Pout j ((dd i) ((dd j) F)) x⟫_ℝ-
      ⟪F.val x,Pout j ((D i) ((dd i) ((dd j) F))) x⟫_ℝ)

/-- Ordinary first-base derivative products, in their distinct i,j order. -/
def nativeOrdinaryRRow (i j : Fin 3) (F : FC) (x : R3) : ℝ :=
  ⟪-(Bnative i F).val x,nativeDerivativePOutput
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q i j ((dd j) F) x⟫_ℝ-
    ⟪F.val x,Pout i ((coefficientDerivative (dd i) (D j)) ((dd j) F)) x⟫_ℝ

/-- Ordinary zero-base derivative products. No negative-space compositions
are formed; the original finite sphere adjoints remain on the test. -/
def nativeOrdinaryZRow (i : Fin 3) (F : FC) (x : R3) : ℝ :=
  ⟪-(Bnative i F).val x,nativeDerivativeQOutput
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p hdr hAr q i F x⟫_ℝ-
    ⟪F.val x,Pout i ((coefficientDerivative (dd i) J) F) x⟫_ℝ

/-- Full actual first-base row, ordinary products plus gained D/Q and J/P. -/
def nativeRFirstDensity (F : FC) (x : R3) : ℝ :=
  ∑ j : Fin 3,
    ((∑ i : Fin 3, nativeOrdinaryRRow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 dr Ar p hdr hAr q i j F x)+
    nativeDZeroCommutatorDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q j F ((dd j) F) x+
    (⟪(Js F).val x,Pout j ((dd j) F) x⟫_ℝ-⟪F.val x,Pout j (J ((dd j) F)) x⟫_ℝ))

/-- Full actual zero-base row, ordinary products plus gained J/Q. -/
def nativeZZeroDensity (F : FC) (x : R3) : ℝ :=
  (∑ i : Fin 3, nativeOrdinaryZRow
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q i F x)+
    (⟪(Js F).val x,Qout F x⟫_ℝ-⟪F.val x,Qout (J F) x⟫_ℝ)

/-- Full signed lower-row scalar, with the original T/R/Z terms exposed. -/
def nativeSignedRowsDensity (F : FC) (x : R3) : ℝ :=
  nativeTSecondDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 dr Ar p hdr hAr q F x+
  nativeRFirstDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q F x+
  nativeZZeroDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q F x

/-- Global exact first/zero split. It is the definition of nativeZeroHalf and
the genuine finite derivative-lift identity, not a substitute physical S. -/
private theorem nativeSOut_eq_first_add_zero (F : FC) (x : R3) :
    SO F x = (∑ j : Fin 3, Pout j ((dd j) F) x)+Qout F x := by
  unfold nativeZeroOut nativeZeroHalf
  have hInputDerivative (j : Fin 3) : directionalFDeriv (coordinateDirection j)
      (ActualHigherSFormation.higherSInput hO hD F) x =
      finiteCoreSobolevLift hO hD (3/2 : ℝ) ((dd j) F) x :=
    directionalFDeriv_finiteCoreSobolevLift hO hD (3/2 : ℝ) F (coordinateDirection j) x
  simp only [ActualHigherSFirstPhysicalCommutatorGraph.coordinateFirstAction,hInputDerivative,
    nativeFirstOut,map_sub,map_sum,ActualHigherSFormation.nativeHigherSOut]
  abel


include hg2 hdr hAr in
private theorem nativeFirstOut_smooth_of_common_room
    (δ : ℝ) (Cm : CRoom δ) (j : Fin 3) (G : FC)
    (hTG : ∀ x ∈ tsupport G.val, (Tq dr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (Pout j G) := by
  have hInput := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) G
  have hC (x : R3) (hx : x ∈ tsupport G.val) : ContDiffAt ℝ ∞
      (fun y => highFirstCoordinateCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q y j) x :=
    contDiffAt_highFirstCoordinateCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ Cm g2 hg2 dr Ar p hdr hAr q j x (hTG x hx)
  have hSmooth := contDiff_supported_operator_apply
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) G)
    (fun y => highFirstCoordinateCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q y j)
    (tsupport G.val) (isClosed_tsupport G.val) hInput
    (ActualHigherSFirstPhysicalCommutatorGraph.higherSInput_eq_zero_off hO hD G) hC
  let v : R3 → SphereSobolev (1/2 : ℝ) := fun y =>
    highFirstCoordinateCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q y j
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) G y)
  have hv : ContDiff ℝ ∞ v := hSmooth
  have hOut : ContDiff ℝ ∞ (fun y => sphereSobolevHalfToSphereL2L hO hD (v y)) :=
    contDiff_halfToSphereL2_apply hO hD v hv
  have hOutput : (fun y => sphereSobolevHalfToSphereL2L hO hD (v y)) = Pout j G := by
    funext y
    simp only [v,ActualLowerUSFirstOutput.nativeFirstOut]
  exact Eq.mp (congrArg (fun f : R3 → SphereL2 => ContDiff ℝ ∞ f) hOutput) hOut

private lemma nativeQOut_lowerAdjoint_expand
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    Qout (LA F) x = (∑ i : Fin 3, Qout ((D i) ((dd i) F)) x)+Qout (J F) x := by
  let term : Fin 3 ⊕ Unit → FC := fun z => match z with
    | Sum.inl i => (D i) ((dd i) F)
    | Sum.inr _ => J F
  have hT0 : ∀ y ∈ tsupport (LA F).val, (Tq dr Ar p q) y ∈ ParamRoom δ :=
    fun y hy => hTF y ((finiteCoreSupportPreserving_nativeULowerAdjointCore
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F) hy)
  have hT : ∀ z : Fin 3 ⊕ Unit, ∀ y ∈ tsupport (term z).val,
      (Tq dr Ar p q) y ∈ ParamRoom δ := by
    intro z y hy
    cases z with
    | inl i =>
      exact hTF y ((finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _ F)
        ((finiteCoreSupportPreserving_nativeULowerAdjointFirstCoefficient
          hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i ((dd i) F)) hy))
    | inr a => exact hTF y ((finiteCoreSupportPreserving_nativeULowerAdjointZeroCoefficient
        hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F) hy)
  have hLift : finiteCoreSobolevLift hO hD (3/2 : ℝ) (LA F) x =
      ∑ z : Fin 3 ⊕ Unit, (1 : ℝ) • finiteCoreSobolevLift hO hD (3/2 : ℝ) (term z) x := by
    unfold nativeULowerAdjointCore modelFirstOrder finiteCoreSobolevLift
    simp only [LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,
      map_add,map_sum,Submodule.coe_add,Submodule.coe_sum,Pi.add_apply,Finset.sum_apply,
      Fintype.sum_sum_type,Fintype.sum_unique,term,one_smul]
  have hQ := nativeZeroOut_weighted_sum_of_lift_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq
    (fun _ : Fin 3 ⊕ Unit => (1:ℝ)) (LA F) term hT0 hT x hLift
  simpa only [Fintype.sum_sum_type,Fintype.sum_unique,term,one_smul] using hQ

/-- Original finite base product rule; both coefficient derivatives remain. -/
private lemma nativeLowerAdjoint_base_expand (F : FC) (j : Fin 3) :
    (dd j) (LA F) =
      (∑ i : Fin 3, ((coefficientDerivative (dd j) (D i)) ((dd i) F)+
        (D i) ((dd i) ((dd j) F))))+
      (coefficientDerivative (dd j) J) F+J ((dd j) F) := by
  have h := congrArg (fun T : Module.End ℝ FC => T F)
    (modelFirstOrder_base_expand (fun i => dd i) (fun i => D i) J j)
  have hComm (i : Fin 3) : (dd j) ((dd i) F) = (dd i) ((dd j) F) :=
    congrArg (fun T : Module.End ℝ FC => T F) (coreDirectionalDerivative_commute hO hD _ _).eq
  simpa only [nativeULowerAdjointCore,LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,hComm] using h

private lemma nativeSOut_lowerAdjoint_expand
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    SO (LA F) x =
      (∑ i : Fin 3, ∑ j : Fin 3, Pout j ((D i) ((dd i) ((dd j) F))) x)+
      (∑ i : Fin 3, ∑ j : Fin 3, Pout i ((coefficientDerivative (dd i) (D j)) ((dd j) F)) x)+
      (∑ i : Fin 3, Pout i ((coefficientDerivative (dd i) J) F) x)+
      (∑ j : Fin 3, Pout j (J ((dd j) F)) x)+
      (∑ i : Fin 3, Qout ((D i) ((dd i) F)) x)+Qout (J F) x := by
  rw [nativeSOut_eq_first_add_zero
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 dr Ar p hdr hAr q (LA F) x,
    nativeQOut_lowerAdjoint_expand
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF x]
  simp only [nativeLowerAdjoint_base_expand,
    nativeFirstOut_add,nativeFirstOut_sum,Finset.sum_add_distrib]
  have hSwap : (∑ j : Fin 3, ∑ i : Fin 3, Pout j ((D i) ((dd i) ((dd j) F))) x) =
      ∑ i : Fin 3, ∑ j : Fin 3, Pout j ((D i) ((dd i) ((dd j) F))) x := Finset.sum_comm
  rw [hSwap]
  abel


include hg2 in
private lemma nativeSOut_base_expand
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ)
    (i : Fin 3) (x : R3) :
    directionalFDeriv (coordinateDirection i) (SO F) x =
      (∑ j : Fin 3,
        (nativeDerivativePOutput
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q i j ((dd j) F) x+
        Pout j ((dd i) ((dd j) F)) x))+
      (nativeDerivativeQOutput
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 dr Ar p hdr hAr q i F x+Qout ((dd i) F) x) := by
  have hP (j : Fin 3) := nativeFirstOut_smooth_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q δ Cm j ((dd j) F)
    (fun y hy => hTF y ((finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _ F) hy))
  have hQ := (nativeZeroOut_regular
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF).1
  have hSplit : SO F = (fun y => (∑ j : Fin 3, Pout j ((dd j) F) y)+Qout F y) :=
    funext (fun y => nativeSOut_eq_first_add_zero
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 dr Ar p hdr hAr q F y)
  simp only [nativeDerivativePOutput,nativeDerivativeQOutput,sub_add_cancel]
  rw [hSplit,directionalFDeriv_add _ _ _ (ContDiff.sum (fun j _ => hP j)) hQ,
    ActualHigherSFirstPhysicalCommutatorGraph.directional_fin_sum
      (fun j : Fin 3 => Pout j ((dd j) F)) hP]

private def actualSignedRowData (F : FC) (x : R3) : SignedRowData where
  test := F.val x
  dtest := fun i => -(Bnative i F).val x
  jtest := (Js F).val x
  p := fun j => Pout j ((dd j) F) x
  q := Qout F x
  pp := fun i j => Pout j ((dd i) ((dd j) F)) x
  dp := fun i j => nativeDerivativePOutput
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q i j ((dd j) F) x
  pd := fun i j => Pout j ((D i) ((dd i) ((dd j) F))) x
  po := fun i j => Pout i ((coefficientDerivative (dd i) (D j)) ((dd j) F)) x
  dq := fun i => nativeDerivativeQOutput
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 dr Ar p hdr hAr q i F x
  qd := fun i => Qout ((dd i) F) x
  pq := fun i => Pout i ((coefficientDerivative (dd i) J) F) x
  qp := fun i => Qout ((D i) ((dd i) F)) x
  pj := fun j => Pout j (J ((dd j) F)) x
  qj := Qout (J F) x

/-- The genuine full-output Green density, after its internally identified
sphere transpose, before the signed T/R/Z regrouping. -/
def nativeSignedBeforeRowsDensity (F : FC) (x : R3) : ℝ :=
  (∑ i : Fin 3, ⟪-(Bnative i F).val x,directionalFDeriv (coordinateDirection i) (SO F) x⟫_ℝ)+
    ⟪(Js F).val x,SO F x⟫_ℝ-⟪F.val x,SO (LA F) x⟫_ℝ

private theorem signed_before_actual_projection
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    nativeSignedBeforeRowsDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F x =
      signedRowRaw (actualSignedRowData
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q F x) := by
  simp only [nativeSignedBeforeRowsDensity,signedRowRaw,actualSignedRowData]
  rw [nativeSOut_eq_first_add_zero
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 dr Ar p hdr hAr q F x,
    nativeSOut_lowerAdjoint_expand
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF x]
  simp_rw [nativeSOut_base_expand
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF]
  simp only [add_assoc]

private theorem signed_grouped_actual_projection (F : FC) (x : R3) :
    signedRowGrouped (actualSignedRowData
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F x) =
      nativeSignedRowsDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q F x := by
  rfl

/-- Exact signed weak row identity for the actual native lower U/S pair.
Every physical S, P and Q output is kept in its original nonfinite domain. -/
theorem nativeSignedBeforeRowsDensity_eq_rows_of_common_room
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    nativeSignedBeforeRowsDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F x =
      nativeSignedRowsDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q F x :=
  (signed_before_actual_projection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF x).trans
    ((signedRowRaw_eq_grouped _).trans (signed_grouped_actual_projection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F x))


/-- Actual signed-row integral identity. Integrability of the complete row
sum follows from the original full-output Green theorem, without a finite-S
output premise. Separate row estimates remain the quantitative next step. -/
theorem actual_lower_US_signed_rows_integral_of_common_room
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) :
    Integrable (fun x => mu x*Lo F x) ∧
    Integrable (fun x => mu x*nativeSignedRowsDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F x) ∧
    (∫ x, mu x*Lo F x) = ∫ x, mu x*nativeSignedRowsDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F x := by
  have hGreen := ActualLowerUSWeightedDomainBridge.actual_lower_S_full_Green_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF
  have hJs : Js = nativeULowerAdjointZeroWeightedTranspose hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr :=
    nativeULowerAdjointZeroWeightedTranspose_eq_of_sphere_adjoint
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr Js
      (nativeULowerAdjointZeroSphereAdjointCore_inner hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr)
  let WB : Fin 3 → R3 → ℝ := fun i x => mu x*⟪(Bnative i F).val x,
    directionalFDeriv (coordinateDirection i) (SO F) x⟫_ℝ
  let WJ : R3 → ℝ := fun x => mu x*⟪(Js F).val x,SO F x⟫_ℝ
  let WP : R3 → ℝ := fun x => mu x*⟪F.val x,SO (LA F) x⟫_ℝ
  have hWB (i : Fin 3) : Integrable (WB i) := hGreen.2.1 i
  have hWJ : Integrable WJ := by simpa only [WJ,hJs] using hGreen.2.2.1
  have hWP : Integrable WP := hGreen.2.2.2.1
  have hSum : Integrable (fun x => ∑ i : Fin 3, -(WB i x)) :=
    integrable_finset_sum _ (fun i _ => (hWB i).neg)
  have hBefore : Integrable (fun x => (∑ i : Fin 3, -(WB i x))+WJ x-WP x) :=
    (hSum.add hWJ).sub hWP
  have hPoint (x : R3) : (∑ i : Fin 3, -(WB i x))+WJ x-WP x =
      mu x*nativeSignedRowsDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q F x := by
    rw [← nativeSignedBeforeRowsDensity_eq_rows_of_common_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF x]
    simp only [WB,WJ,WP,nativeSignedBeforeRowsDensity,inner_neg_left,
      Finset.mul_sum,mul_add,mul_sub,mul_neg]
  have hRows : Integrable (fun x => mu x*nativeSignedRowsDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F x) := hBefore.congr (Eventually.of_forall hPoint)
  refine ⟨hGreen.1,hRows,?_⟩
  calc
    _ = -(∑ i : Fin 3, ∫ x, WB i x)+(∫ x, WJ x)-∫ x, WP x := by
      simpa only [WB,WJ,WP,hJs] using hGreen.2.2.2.2
    _ = (∑ i : Fin 3, ∫ x, -(WB i x))+(∫ x, WJ x)-∫ x, WP x := by
      simp only [integral_neg,Finset.sum_neg_distrib]
    _ = ∫ x, (∑ i : Fin 3, -(WB i x))+WJ x-WP x := by
      exact integral_fintype_sum_add_sub (fun (i : Fin 3) (x : R3) => -(WB i x))
        WJ WP (fun i => (hWB i).neg) hWJ hWP
    _ = _ := integral_congr_ae (Eventually.of_forall hPoint)


/-- Original-parameter-order structural identity; no norm callback is assumed. -/
theorem exists_actual_lower_US_signed_rows_integral
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ etaRows : ℝ, 0 < etaRows ∧ etaRows ≤ data.eta0 ∧ etaRows ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaRows →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*
        (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤
          eta*referenceRadius dr Ar p L x) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*nativeULowerSCrossDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q F x) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*nativeSignedRowsDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q F x) ∧
      (∫ x, referenceDensityFamily g L (q,x)*nativeULowerSCrossDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q F x) =
      ∫ x, referenceDensityFamily g L (q,x)*nativeSignedRowsDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q F x
 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨etaF,hEtaF,hEtaF1,hGuard⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ δ Cm.rev.pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaRows := min data.eta0 etaF
  have hEtaRows : 0 < etaRows := lt_min data.eta0_pos hEtaF
  have hR0 : etaRows ≤ data.eta0 := min_le_left _ _
  have hRF : etaRows ≤ etaF := min_le_right _ _
  refine ⟨etaRows,hEtaRows,hR0,hRF.trans hEtaF1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRows K _hK hBall F hSupp hb hs _hH8
  have hTF (x : R3) (hx : x ∈ tsupport F.val) :
      (ActualHigherSFormation.higherSParam L dr Ar p q) x ∈ ParamRoom δ := by
    have hxK := hSupp hx
    have hxClosed : x ∈ closedBall y0 ρ := ball_subset_closedBall (hBall hxK)
    have hg := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaRows.trans hRF)
      x hxClosed (hBall hxK) (hb x hxK) (hs x hxK)
    exact (higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x hg).self_of_nhds
  exact actual_lower_US_signed_rows_integral_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSignedRows
