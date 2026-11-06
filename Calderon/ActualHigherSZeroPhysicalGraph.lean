import Calderon.ActualHigherSZeroCoefficientJets
import Calderon.ActualHigherSFirstPhysicalCommutatorGraph
import Calderon.ActualCommonQuadraticFormationConsumer
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroPhysicalGraph
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  PrincipalCommutator ActualHigherSScalarCommutatorNativeForm ActualHigherSFirstPhysicalCommutatorGraph
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
section FirstActionTransfer
variable {E H0 M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H0] [NormedSpace ℝ H0]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
/-- Normalize the checked whole first-action transfer before native instantiation. -/
private lemma coordinateFirstAction_graph
    (I : E →L[ℝ] M) (J : H0 →L[ℝ] N)
    (BH : Fin 3 → R3 → (E →L[ℝ] H0)) (BL : Fin 3 → R3 → (M →L[ℝ] N))
    (u : R3 → E) (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0)
    (hGraph : ∀ l, ∀ x ∈ K, ∀ v : E, J (BH l x v) = BL l x (I v)) (x : R3) :
    J (coordinateFirstAction BH u x) =
      ∑ l : Fin 3, BL l x (I (directionalFDeriv (coordinateDirection l) u x)) := by
  have ht := congrFun (coordinateFirstAction_transfer I J BH BL u K hK hu h0 hGraph) x
  have hr : coordinateFirstAction BL (fun y => I (u y)) x =
      ∑ l : Fin 3, BL l x (I (directionalFDeriv (coordinateDirection l) u x)) := by
    unfold coordinateFirstAction
    apply Finset.sum_congr rfl
    intro l _
    exact congrArg (BL l x)
      (ActualHigherSFirstPhysicalCommutatorGraph.directional_linear_input I u hu (coordinateDirection l) x)
  exact ht.trans hr
end FirstActionTransfer

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
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HCC" => highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BCC" => ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "SH" => ActualHigherSFormation.nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

attribute [local irreducible] ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient highFirstCoordinateCoefficient
  ActualHigherSFormation.nativeHigherSHalf ActualHigherSFormation.nativeHigherSNegative
  ActualHigherSFormation.higherSParam sphereSobolevInclusionL

/-- Explicit Half realization of the zero field on the actual finite input. -/
def nativeZeroHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  SH δr Ar p hδr hAr q hreg δ0 W g2 F x -
    coordinateFirstAction (fun l y => HCC g2 δr Ar p q y l) (UF F) x
local notation "ZH" => nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Global exact graph from full formation and supported first-action transfer. -/
theorem nativeZeroHalf_negative_graph
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    JL (ZH hreg δ0 W g2 δr Ar p hδr hAr q F x) = CZc g2 δr Ar p q x (UF F x) := by
  let bh : Fin 3 → R3 → (Hi →L[ℝ] Half) := fun l y => HCC g2 δr Ar p q y l
  let bl : Fin 3 → R3 → (Half →L[ℝ] Neg) := fun l y => BCC g2 δr Ar p q y l
  have hu : ContDiff ℝ ∞ (UF F) := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have h0 : ∀ y ∉ tsupport F.val, UF F y = 0 := higherSInput_eq_zero_off hO hD F
  have hgraph : ∀ l, ∀ y ∈ tsupport F.val, ∀ v : Hi, JL (bh l y v) = bl l y (IH v) := by
    intro l y hy v
    exact highFirstCoordinateCoefficient_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 δr Ar p q l y (hTF y hy) v
  have hFirst := coordinateFirstAction_graph IH JL bh bl (UF F) (tsupport F.val)
    (isClosed_tsupport F.val) hu h0 hgraph x
  have hS := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2
      δr Ar p hδr hAr q hq F hTF
  have hWhole := congrFun (ActualHigherSZeroCoefficientJets.actual_higherS_canonical_zero_field
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
      g2 δr Ar p hδr hAr q hq F hTF) x
  unfold nativeZeroHalf
  rw [map_sub]
  have hValue := (hS.2.2.2.1 x).trans hWhole
  exact (congrArg₂ (fun u v : Neg => u-v) hValue hFirst).trans (add_sub_cancel_left _ _)


/-- Support is inherited from the exact native formation and the supported first action. -/
lemma nativeZeroHalf_eq_zero_off
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (hx : x ∉ tsupport F.val) :
    ZH hreg δ0 W g2 δr Ar p hδr hAr q F x = 0 := by
  have hS := ActualHigherSFormation.nativeHigherSHalf_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W g2 F x hx
  have hFirst := coordinateFirstAction_eq_zero_off
    (fun l y => HCC g2 δr Ar p q y l) (UF F) (tsupport F.val) (isClosed_tsupport F.val)
      (higherSInput_eq_zero_off hO hD F) x hx
  simp only [nativeZeroHalf,hS,hFirst,sub_self]

/-- Genuine smooth compact full Half field, with support inside the original input support. -/
theorem nativeZeroHalf_regular
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (ZH hreg δ0 W g2 δr Ar p hδr hAr q F) ∧
      tsupport (ZH hreg δ0 W g2 δr Ar p hδr hAr q F) ⊆ tsupport F.val ∧
      HasCompactSupport (ZH hreg δ0 W g2 δr Ar p hδr hAr q F) := by
  let bh : Fin 3 → R3 → (Hi →L[ℝ] Half) := fun l y => HCC g2 δr Ar p q y l
  have hu : ContDiff ℝ ∞ (UF F) := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hbh : ∀ l, ∀ x ∈ tsupport F.val, ContDiffAt ℝ ∞ (bh l) x := by
    intro l x hx
    exact contDiffAt_highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q l x (hTF x hx)
  have hFirst := contDiff_coordinateFirstAction bh (UF F) (tsupport F.val) (isClosed_tsupport F.val)
    hu (higherSInput_eq_zero_off hO hD F) hbh
  have hS := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2
      δr Ar p hδr hAr q hq F hTF
  have hs : ContDiff ℝ ∞ (ZH hreg δ0 W g2 δr Ar p hδr hAr q F) := hS.2.2.1.sub hFirst
  have hSupp : Function.support (ZH hreg δ0 W g2 δr Ar p hδr hAr q F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hx'
    exact hx (nativeZeroHalf_eq_zero_off g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F x hx')
  exact ⟨hs,closure_minimal hSupp (isClosed_tsupport F.val),F.property.2.1.mono' hSupp⟩

/-- The full SphereL2 realization, using the existing Half-to-SphereL2 map. -/
def nativeZeroOut (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  sphereSobolevHalfToSphereL2L hO hD (ZH hreg δ0 W g2 δr Ar p hδr hAr q F x)
local notation "ZO" => nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact graph of the full physical output, with no finite-output requirement. -/
theorem nativeZeroOut_negative_graph
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ZO hreg δ0 W g2 δr Ar p hδr hAr q F x)) =
      CZc g2 δr Ar p q x (UF F x) :=
  (sphereSobolevHalfToSphereL2L_negative_compatibility hO hD _).trans
    (nativeZeroHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F hTF x)

/-- Smooth compact full physical zero field supported inside the original finite input support. -/
theorem nativeZeroOut_regular
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (ZO hreg δ0 W g2 δr Ar p hδr hAr q F) ∧
      tsupport (ZO hreg δ0 W g2 δr Ar p hδr hAr q F) ⊆ tsupport F.val ∧
      HasCompactSupport (ZO hreg δ0 W g2 δr Ar p hδr hAr q F) := by
  have hz := nativeZeroHalf_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F hTF
  have hs : ContDiff ℝ ∞ (ZO hreg δ0 W g2 δr Ar p hδr hAr q F) :=
    (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hz.1
  have hSupp : Function.support (ZO hreg δ0 W g2 δr Ar p hδr hAr q F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hx'
    apply hx
    show sphereSobolevHalfToSphereL2L hO hD (ZH hreg δ0 W g2 δr Ar p hδr hAr q F x) = 0
    rw [nativeZeroHalf_eq_zero_off g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F x hx',map_zero]
  exact ⟨hs,closure_minimal hSupp (isClosed_tsupport F.val),F.property.2.1.mono' hSupp⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroPhysicalGraph
