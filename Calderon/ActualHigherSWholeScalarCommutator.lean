import Calderon.ActualHigherSZeroPhysicalForm
import Calderon.ActualHigherSFirstPhysicalCommutatorGraph
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSWholeScalarCommutator
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  PrincipalCommutator ActualScalarPrincipalAdjoint PerturbedDensityAdjoint
  ActualHigherSScalarCommutatorNativeForm ActualHigherSFirstPhysicalCommutatorGraph
  ActualHigherSZeroPhysicalGraph ActualHigherSZeroPhysicalCommutatorGraph ActualHigherSZeroPhysicalForm
section Algebra
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
private lemma directional_sub_graph (u v : R3 → V) (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (X x : R3) :
    directionalFDeriv X (fun y => u y-v y) x = directionalFDeriv X u x-directionalFDeriv X v x := by
  have he := ((hu.differentiable (by simp) x).hasFDerivAt.sub
    (hv.differentiable (by simp) x).hasFDerivAt).fderiv
  have hfun : u-v = (fun y => u y-v y) := by funext y; rfl
  rw [hfun] at he
  simpa only [directionalFDeriv,ContinuousLinearMap.sub_apply] using
    congrArg (fun A : R3 →L[ℝ] V => A X) he

private lemma coordinateSecondAction_sub (a : Fin 3 → Fin 3 → R3 → ℝ)
    (u v : R3 → V) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    coordinateSecondAction a (fun y => u y-v y) =
      fun y => coordinateSecondAction a u y-coordinateSecondAction a v y := by
  have hY (Y : R3) : directionalFDeriv Y (fun y => u y-v y) =
      fun y => directionalFDeriv Y u y-directionalFDeriv Y v y :=
    funext (fun y => directional_sub_graph u v hu hv Y y)
  have hXY (X Y x : R3) :
      directionalFDeriv X (directionalFDeriv Y (fun y => u y-v y)) x =
        directionalFDeriv X (directionalFDeriv Y u) x-directionalFDeriv X (directionalFDeriv Y v) x := by
    rw [hY Y]
    exact directional_sub_graph _ _ (contDiff_directionalFDeriv Y u hu)
      (contDiff_directionalFDeriv Y v hv) X x
  funext x
  simp only [coordinateSecondAction,hXY,smul_sub,Finset.sum_sub_distrib]
end Algebra
section Additive
variable {V : Type*} [AddCommGroup V]
private lemma commutator_split_value (a b c d : V) :
    a-c = (b-d)+((a-b)-(c-d)) := by abel
end Additive
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "BETA" => actualReferenceBeta g L
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "SH" => ActualHigherSFormation.nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "ZH" => nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HCC" => highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FC" => nativeFirstPhysicalCommutatorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FO" => nativeFirstPhysicalCommutatorOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZC" => nativeScalarZeroPhysicalCommutatorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZO" => nativeScalarZeroPhysicalCommutatorOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
attribute [local irreducible] ActualHigherSFormation.nativeHigherSHalf highFirstCoordinateCoefficient
  coreCoordinateSecondAction nativeZeroHalf nativeScalarZeroPhysicalCommutatorHalf
  coordinateSecondAction

/-- The whole commutator is defined by the original full S action difference. -/
def nativeWholeScalarCommutatorHalf
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  let ha : ∀ i j, ContDiff ℝ ∞ (aa i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  let FA := coreCoordinateSecondAction hO hD aa ha F
  SH δr Ar p hδr hAr q hreg δ0 W g2 FA x-
    coordinateSecondAction aa (SH δr Ar p hδr hAr q hreg δ0 W g2 F) x
local notation "WC" => nativeWholeScalarCommutatorHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def nativeWholeScalarCommutatorOut
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  sphereSobolevHalfToSphereL2L hO hD (WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F x)
local notation "WO" => nativeWholeScalarCommutatorOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact whole Half split; the full physical output is not projected to a finite band. -/
theorem nativeWholeScalarCommutatorHalf_eq_first_add_zero
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F =
      fun x => FC g2 δr Ar p q h F x+ZC hreg δ0 W g2 δr Ar p hδr hAr q h hh F x := by
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  have ha : ∀ i j, ContDiff ℝ ∞ (aa i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  let FA := coreCoordinateSecondAction hO hD aa ha F
  let bh : Fin 3 → R3 → (Hi →L[ℝ] Half) := fun l y => HCC g2 δr Ar p q y l
  let SF := SH δr Ar p hδr hAr q hreg δ0 W g2 F
  let SA := SH δr Ar p hδr hAr q hreg δ0 W g2 FA
  let BF := coordinateFirstAction bh (UF F)
  let BA := coordinateFirstAction bh (UF FA)
  have hUA : UF FA = coordinateSecondAction aa (UF F) :=
    finiteCoreSobolevLift_coreCoordinateSecondAction hO hD (3/2 : ℝ) aa ha F
  have hBA : BA = coordinateFirstAction bh (coordinateSecondAction aa (UF F)) :=
    congrArg (coordinateFirstAction bh) hUA
  have hS := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2
      δr Ar p hδr hAr q hq F hTF
  have hSF : ContDiff ℝ ∞ SF := hS.2.2.1
  have hu : ContDiff ℝ ∞ (UF F) := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hbh : ∀ l, ∀ x ∈ tsupport F.val, ContDiffAt ℝ ∞ (bh l) x := by
    intro l x hx
    exact contDiffAt_highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q l x (hTF x hx)
  have hBF : ContDiff ℝ ∞ BF := contDiff_coordinateFirstAction bh (UF F) (tsupport F.val)
    (isClosed_tsupport F.val) hu (higherSInput_eq_zero_off hO hD F) hbh
  have hAZ := coordinateSecondAction_sub aa SF BF hSF hBF
  have hZF : ZH hreg δ0 W g2 δr Ar p hδr hAr q F = fun x => SF x-BF x := by
    funext x
    unfold nativeZeroHalf
    rfl
  funext x
  have hWhole : WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F x = SA x-coordinateSecondAction aa SF x := rfl
  have hFirst : FC g2 δr Ar p q h F x = BA x-coordinateSecondAction aa BF x := by
    unfold nativeFirstPhysicalCommutatorHalf coordinateCommutator
    exact congrArg (fun v : Half => v-coordinateSecondAction aa BF x) (congrFun hBA x).symm
  have hZA : ZH hreg δ0 W g2 δr Ar p hδr hAr q FA x = SA x-BA x := by
    unfold nativeZeroHalf
    rfl
  have hZero : ZC hreg δ0 W g2 δr Ar p hδr hAr q h hh F x =
      (SA x-BA x)-(coordinateSecondAction aa SF x-coordinateSecondAction aa BF x) := by
    unfold nativeScalarZeroPhysicalCommutatorHalf nativeZeroPhysicalCommutatorHalf
    dsimp only [FA,aa] at hZA
    rw [hZA,hZF,congrFun hAZ x]
  exact hWhole.trans ((commutator_split_value (SA x) (BA x)
    (coordinateSecondAction aa SF x) (coordinateSecondAction aa BF x)).trans
      (congrArg₂ (fun u v : Half => u+v) hFirst.symm hZero.symm))

theorem nativeWholeScalarCommutatorOut_eq_first_add_zero
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F =
      fun x => FO g2 δr Ar p q h F x+ZO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x := by
  have hs := nativeWholeScalarCommutatorHalf_eq_first_add_zero g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq h hh F hTF
  funext x
  exact (congrArg (sphereSobolevHalfToSphereL2L hO hD) (congrFun hs x)).trans (map_add _ _ _)

/-- Whole scalar/S physical form with the original energy and before-profile constant. -/
def ActualWholeScalarPhysicalFormBound
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 →
    ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    ∀ hh : (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)),
    ∀ F : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x ∈ tsupport F.val, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
      (∀ x ∈ tsupport F.val, 1 ≤ BETA q δr Ar p x) →
      (∀ x ∈ tsupport F.val, referenceRadius δr Ar p L x*(BETA q δr Ar p x)^2 ≤ eps) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        ⟪F.val x,WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*
        ⟪F.val x,WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ| ≤
        K*eps*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x
local notation "WholeForm" => ActualWholeScalarPhysicalFormBound
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

theorem exists_actual_whole_scalar_physical_reference_form
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hL : 0 < L) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    WholeForm hreg δ0 W δ g2 := by
  obtain ⟨K1,hK1,hcap1⟩ := exists_actual_scalar_first_physical_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
  obtain ⟨K0,hK0,hcap0⟩ := exists_actual_scalar_zero_physical_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac hL g2 hg2
  refine ⟨K1+K0,add_pos hK1 hK0,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F hTF hjet hbeta hsmall
  have h1 := hcap1 δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F hTF hjet hbeta hsmall
  have h0 := hcap0 δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F hTF hjet hbeta hsmall
  have hs := nativeWholeScalarCommutatorOut_eq_first_add_zero g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq h hh F hTF
  have he : (fun x => referenceDensityFamily g L (q,x)*
      ⟪F.val x,WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ) =
      (fun x => referenceDensityFamily g L (q,x)*⟪F.val x,FO g2 δr Ar p q h F x⟫_ℝ+
        referenceDensityFamily g L (q,x)*⟪F.val x,ZO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ) := by
    funext x
    rw [congrFun hs x,inner_add_right,mul_add]
  have hwi : Integrable (fun x => referenceDensityFamily g L (q,x)*
      ⟪F.val x,WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ) := he.symm ▸ (h1.1.add h0.1)
  have hi := congrArg (fun J : R3 → ℝ => ∫ x, J x) he
  rw [integral_add h1.1 h0.1] at hi
  refine ⟨hwi,h1.2.1,?_⟩
  calc
    _ = |(∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,FO g2 δr Ar p q h F x⟫_ℝ)+
        (∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,ZO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ)| :=
      congrArg abs hi
    _ ≤ |∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,FO g2 δr Ar p q h F x⟫_ℝ|+
        |∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,ZO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ| :=
      abs_add_le _ _
    _ ≤ K1*eps*(∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x)+
        K0*eps*(∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) :=
      add_le_add h1.2.2 h0.2.2
    _ = (K1+K0)*eps*(∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) := by ring

theorem exists_retained_actual_whole_scalar_physical_reference_form
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ _Cm : CRoom hreg δ0 W δ,
      (∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → WholeForm hreg δ0 W δ g2 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_whole_scalar_physical_reference_form g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hJac hL g2 hg2


local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "SN" => ActualHigherSFormation.nativeHigherSNegative hF hO hD
  g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
attribute [local irreducible] ActualHigherSFormation.nativeHigherSNegative sphereSobolevInclusionL

/-- Genuine smooth compact whole Half commutator with the original input support. -/
theorem nativeWholeScalarCommutatorHalf_regular
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F) ∧
      tsupport (WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F) ⊆ tsupport F.val ∧
      HasCompactSupport (WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F) := by
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  have ha : ∀ i j, ContDiff ℝ ∞ (aa i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  let FA := coreCoordinateSecondAction hO hD aa ha F
  have hsub : tsupport FA.val ⊆ tsupport F.val := coreCoordinateSecondAction_tsupport hO hD aa ha F
  have hTA : ∀ x ∈ tsupport FA.val, (Tq δr Ar p q) x ∈ ParamRoom δ :=
    fun x hx => hTF x (hsub hx)
  have hsF := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F hTF
  have hsA := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq FA hTA

  have hs : ContDiff ℝ ∞ (WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F) :=
    hsA.2.2.1.sub (contDiff_coordinateSecondAction aa _ ha hsF.2.2.1)
  have hz : ∀ x ∉ tsupport F.val, WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F x = 0 := by
    intro x hx
    have hxA : x ∉ tsupport FA.val := fun ht => hx (hsub ht)
    have hzA := ActualHigherSFormation.nativeHigherSHalf_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
      hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W g2 FA x hxA
    have hzF : ∀ y ∉ tsupport F.val, SH δr Ar p hδr hAr q hreg δ0 W g2 F y = 0 :=
      fun y hy => ActualHigherSFormation.nativeHigherSHalf_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
        hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W g2 F y hy
    have hAz := coordinateSecondAction_eq_zero_off aa _ (tsupport F.val) (isClosed_tsupport F.val) hzF x hx
    dsimp only [FA,aa] at hzA hAz
    simp only [nativeWholeScalarCommutatorHalf,hzA,hAz,sub_self]
  have hSupp : Function.support (WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hx'
    exact hx (hz x hx')
  exact ⟨hs,closure_minimal hSupp (isClosed_tsupport F.val),F.property.2.1.mono' hSupp⟩

/-- The whole commutator's original negative graph follows from GLOBAL formation identities. -/
theorem nativeWholeScalarCommutatorHalf_negative_graph
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    JL (WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F x) =
      SN g2 q (referenceRadius δr Ar p L) (coordinateSecondAction
        (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j) (UF F)) x-
      coordinateSecondAction (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j)
        (fun y => SN g2 q (referenceRadius δr Ar p L) (UF F) y) x := by
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  have ha : ∀ i j, ContDiff ℝ ∞ (aa i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  let FA := coreCoordinateSecondAction hO hD aa ha F
  have hsub : tsupport FA.val ⊆ tsupport F.val := coreCoordinateSecondAction_tsupport hO hD aa ha F
  have hTA : ∀ x ∈ tsupport FA.val, (Tq δr Ar p q) x ∈ ParamRoom δ :=
    fun x hx => hTF x (hsub hx)
  have hsF := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F hTF
  have hsA := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq FA hTA

  have hUA : UF FA = coordinateSecondAction aa (UF F) :=
    finiteCoreSobolevLift_coreCoordinateSecondAction hO hD (3/2 : ℝ) aa ha F
  have hLeft := (hsA.2.2.2.1 x).trans
    (congrArg (fun u : R3 → Hi => SN g2 q (referenceRadius δr Ar p L) u x) hUA)
  have hGlobal : (fun y => JL (SH δr Ar p hδr hAr q hreg δ0 W g2 F y)) =
      fun y => SN g2 q (referenceRadius δr Ar p L) (UF F) y := funext hsF.2.2.2.1
  have hTransfer := coordinateSecondAction_transfer JL aa
    (SH δr Ar p hδr hAr q hreg δ0 W g2 F) hsF.2.2.1
  have hRight := (congrFun hTransfer x).trans
    (congrArg (fun v : R3 → Neg => coordinateSecondAction aa v x) hGlobal)
  dsimp only [FA,aa] at hLeft hRight
  unfold nativeWholeScalarCommutatorHalf
  rw [map_sub]
  exact congrArg₂ (fun u v : Neg => u-v) hLeft hRight

/-- Full smooth compact physical output; no finite-output angular restriction is imposed. -/
theorem nativeWholeScalarCommutatorOut_regular
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F) ∧
      tsupport (WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F) ⊆ tsupport F.val ∧
      HasCompactSupport (WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F) := by
  have hr := nativeWholeScalarCommutatorHalf_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq h hh F hTF
  have hs : ContDiff ℝ ∞ (WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F) :=
    (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hr.1
  have hSupp : Function.support (WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hx'
    apply hx
    have hz : WC hreg δ0 W g2 δr Ar p hδr hAr q h hh F x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx' (hr.2.1 ht))
    simp only [nativeWholeScalarCommutatorOut,hz,map_zero]
  exact ⟨hs,closure_minimal hSupp (isClosed_tsupport F.val),F.property.2.1.mono' hSupp⟩

theorem nativeWholeScalarCommutatorOut_negative_graph
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x)) =
      SN g2 q (referenceRadius δr Ar p L) (coordinateSecondAction
        (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j) (UF F)) x-
      coordinateSecondAction (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j)
        (fun y => SN g2 q (referenceRadius δr Ar p L) (UF F) y) x :=
  (sphereSobolevHalfToSphereL2L_negative_compatibility hO hD _).trans
    (nativeWholeScalarCommutatorHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq h hh F hTF x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSWholeScalarCommutator
